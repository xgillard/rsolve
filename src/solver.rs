use std::clone::Clone;

use utils::*;
use core::*;
use collections::*;

type Watcher = Alias<Clause>;
type Conflict= Alias<Clause>;

// -----------------------------------------------------------------------------------------------
/// # Conflict
/// A simple algebraic type to explicit the fact that some clause is conflicting
// -----------------------------------------------------------------------------------------------
#[derive(Debug)]
pub struct Solver {
    trail       : Trail,
    constraints : Vec<Aliasable<Clause>>,
    learned     : Vec<Aliasable<Clause>>,

    /// Watchers: vectors of watchers associated with each literal.
    /// _Important Notice_ : A clause should watch a literal it owns, not its negation !
    watchers    : LitIdxVec<Vec<Watcher>>,
}

impl Solver {
    pub fn new(nb_vars: usize) -> Solver {
        let mut solver = Solver {
            trail : Trail {
                prop_queue: Vec::with_capacity(nb_vars),
                propagated: 0,
                valuation : Valuation::new(nb_vars)
            },
            constraints : vec![],
            learned     : vec![],
            watchers    : LitIdxVec::with_capacity(nb_vars)
        };

        // initialize empty watchers lists
        for _ in 0..3 {
            solver.watchers.push_values(vec![], vec![]);
        }

        return solver;
    }

	/// This method propagates the information about all the literals that have been
	/// enqueued. It returns an optional conflicting clause whenever conflict is detected
	/// Otherwise, None is returned.
    fn propagate(&mut self) -> Option<Conflict> {
        loop {
            if self.trail.propagated >= self.trail.prop_queue.len() { break }

            let nb_propagated = self.trail.propagated;
            let literal = self.trail.prop_queue[nb_propagated];

            let conflict = self.propagate_literal(literal);
            if conflict.is_some() {
                return conflict;
            }

            self.trail.propagated += 1;
        }
        return None;
    }

	/// Notifies all the watchers of `lit` that `lit` has been falsified.
	/// This method optionally returns a conflicting clause if one is found.
    fn propagate_literal(&mut self, lit : Literal) -> Option<Conflict> {
        for i in 0..self.watchers[lit].len() {
            let watcher = self.watchers[lit][i].clone();
            self.watchers[lit].swap_remove(i);

            match watcher.get_mut() {
                None         => { /* The clause was deteted, hence the watcher can be ignored */ },
                Some(clause) => {
                    match clause.find_new_literal(lit, &self.trail.valuation) {
                        Ok (l) => {
                            // l was found, its ok. We only need to start watching it
                            self.watchers[l].push(watcher.clone());
                        },
                        Err(l) => {
                            // No result could be found, so we need to keep watching `lit`
                            self.watchers[lit].push(watcher.clone());
                            // In the meantime we also need to assign `l`, otherwise the whole
                            // clause is going to be unsat
                            match self.trail.assign(l) {
                                // Assignment went on well, we're done
                                Ok(()) => { },
                                // Conflict detected, return it !
                                Err(())=> return Some(watcher.clone())
                            }
                        }
                    }
                }
            }
        }

        return None;
    }
}

// -----------------------------------------------------------------------------------------------
/// # Valuation
/// This struct encapsulates the idea of an assignment of Variables to Bool values.
// -----------------------------------------------------------------------------------------------
#[derive(Debug)]
pub struct Valuation {
    pub var_value : VarIdxVec<Bool>
}

impl Valuation {

    pub fn new(nb_vars: usize) -> Valuation {
        let mut valuation = Valuation{ var_value: VarIdxVec::with_capacity(nb_vars) };
        for _ in 0..nb_vars { valuation.var_value.push(Bool::Undef); }
        return valuation;
    }

    pub fn get_value(&self, l: Literal) -> Bool {
        let value = self.var_value[l.var()];

        match l.sign() {
            Sign::Positive =>  value,
            Sign::Negative => !value
        }
    }

    pub fn set_value(&mut self, l: Literal, v : Bool) {
        match l.sign() {
            Sign::Positive => self.var_value[l.var()] =  v,
            Sign::Negative => self.var_value[l.var()] = !v
        }
    }

    pub fn is_undef(&self, l: Literal) -> bool {
        self.var_value[l.var()] == Bool::Undef
    }
    pub fn is_true (&self, l: Literal) -> bool {
        match l.sign() {
            Sign::Positive => self.var_value[l.var()] == Bool::True,
            Sign::Negative => self.var_value[l.var()] == Bool::False,
        }
    }
    pub fn is_false(&self, l: Literal) -> bool {
        match l.sign() {
            Sign::Positive => self.var_value[l.var()] == Bool::False,
            Sign::Negative => self.var_value[l.var()] == Bool::True,
        }
    }
}

// -----------------------------------------------------------------------------------------------
/// # Trail
/// The structure that memorizes the state and order in which literals have been assigned
// -----------------------------------------------------------------------------------------------
#[derive(Debug)]
pub struct Trail {
    valuation  : Valuation,
    prop_queue : Vec<Literal>,
    propagated : usize
}

impl Trail {
    /// Assigns a given literal to True. That is to say, it assigns a value to the given literal
    /// in the Valuation and it enqueues the negation of the literal on the propagation queue
    ///
    /// # Note
    /// We always push the *negation* of the assigned literal on the stack
    fn assign(&mut self, lit: Literal) -> Result<(), ()> {
        match self.valuation.get_value(lit) {
            Bool::True  => Ok(()),
            Bool::False => Err(()),
            Bool::Undef => {
                self.valuation.set_value(lit, Bool::True);
                self.prop_queue.push(!lit);
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod test_solver {
    use super::*;

    #[test]
    fn propagate_processes_everything_until_a_fixed_point_is_reached(){
        let mut solver = Solver::new(3);

        // initialize the constraint database
        add_clause(&mut solver, vec![1, -2, -3]);
        add_clause(&mut solver, vec![2, -3]);
        add_clause(&mut solver, vec![3]);

        // start the test (for real !)
        solver.trail.assign(Literal::from(3)).expect("3 should be assignable");

        assert_eq!(solver.trail.propagated, 0);
        assert_eq!(solver.trail.prop_queue, vec![lit(-3)]);

        assert!(solver.propagate().is_none());

        assert_eq!(solver.trail.propagated, 3);
        assert_eq!(solver.trail.prop_queue, vec![lit(-3), lit(-2), lit(-1)]);
    }

    #[test]
    fn propagate_stops_when_a_conflict_is_detected() {
        let mut solver = Solver::new(3);

        // initialize the constraint database
        add_clause(&mut solver, vec![ 1, -2, -3]);
        add_clause(&mut solver, vec![ 2, -3]);
        add_clause(&mut solver, vec![ 3]);
        add_clause(&mut solver, vec![-2]);

        // start the test (for real !)
        solver.trail.assign(Literal::from( 3)).expect(" 3 should be assignable");
        solver.trail.assign(Literal::from(-2)).expect("-2 should be assignable");

        let conflict = solver.propagate();
        assert_eq!("Some(Alias(Some(Clause([Literal(2), Literal(-3)]))))", format!("{:?}", conflict));
        assert_eq!(solver.trail.prop_queue, vec![lit(-3), lit(2)])
    }

    // TODO this should be part of the standard solver API
    fn add_clause(s: &mut Solver, c :Vec<iint>) {
        let ls : Vec<Literal> = c.iter()
                                    .take(2)
                                    .map(|l| lit(*l))
                                    .collect();

        s.constraints.push( clause(c) );

        for l in ls {
            s.watchers[l].push(s.constraints.last().unwrap().alias());
        }
    }

    fn lit(l: iint) -> Literal {
        Literal::from(l)
    }
    fn clause(v : Vec<iint>) -> Aliasable<Clause> {
        Aliasable::new(
            Clause::new(
                v.iter()
                        .map(|l| Literal::from(*l))
                        .collect()
            ))
    }
}