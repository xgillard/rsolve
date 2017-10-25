use std::clone::Clone;
use std::ops::*;

use utils::*;
use core::*;
use flags::*;
use collections::*;

type Watcher = Alias<Clause>;
type Conflict= Alias<Clause>;
type Reason  = Alias<Clause>;

// -----------------------------------------------------------------------------------------------
/// # Conflict
/// A simple algebraic type to explicit the fact that some clause is conflicting
// -----------------------------------------------------------------------------------------------
#[derive(Debug)]
pub struct Solver {
    pub trail       : Trail,
    pub constraints : Vec<Aliasable<Clause>>,
    pub learned     : Vec<Aliasable<Clause>>,

    /// Watchers: vectors of watchers associated with each literal.
    /// _Important Notice_ : A clause should watch a literal it owns, not its negation !
    pub watchers    : LitIdxVec<Vec<Watcher>>,
    /// The flags associated with each literal
    pub flags       : LitIdxVec<Flags>,
}

impl Solver {
    pub fn new(nb_vars: usize) -> Solver {
        let mut solver = Solver {
            trail : Trail {
                forced    : 0,
                propagated: 0,
                prop_queue: Vec::with_capacity(nb_vars),
                valuation : Valuation::new(nb_vars)
            },
            constraints : vec![],
            learned     : vec![],
            watchers    : LitIdxVec::with_capacity(nb_vars),
            flags       : LitIdxVec::with_capacity(nb_vars)
        };

        // initialize empty watchers lists
        for _ in 0..nb_vars {
            solver.watchers.push_values(vec![], vec![]);
            solver.flags   .push_values(Flags::new(), Flags::new());
        }

        return solver;
    }

    pub fn add_problem_clause(&mut self, c :Vec<iint>) {
        let watched: Vec<Literal> = c.iter()
                                     .take(2)
                                     .map(|l|Literal::from(*l))
                                     .collect();

        let clause = Aliasable::new(Clause::from(c));

        self.constraints.push( clause);

        for l in watched {
            self.watchers[l].push(self.constraints.last().unwrap().alias());
        }
    }
    pub fn add_learned_clause(&mut self, c :Vec<iint>) {
        let watched: Vec<Literal> = c.iter()
            .take(2)
            .map(|l|Literal::from(*l))
            .collect();

        let clause = Aliasable::new(Clause::from(c));

        self.learned.push( clause);

        for l in watched {
            self.watchers[l].push(self.learned.last().unwrap().alias());
        }
    }

    // -------------------------------------------------------------------------------------------//
    // ---------------------------- PROPAGATION --------------------------------------------------//
    // -------------------------------------------------------------------------------------------//

	/// This method propagates the information about all the literals that have been
	/// enqueued. It returns an optional conflicting clause whenever conflict is detected
	/// Otherwise, None is returned.
    pub fn propagate(&mut self) -> Option<Conflict> {
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
    pub fn propagate_literal(&mut self, lit : Literal) -> Option<Conflict> {
        for _ in 0..self.watchers[lit].len() {
            // remove the head of the list, always
            let watcher = self.watchers[lit][0].clone();
            self.watchers[lit].swap_remove(0);

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
                            match self.trail.assign(l, Some(watcher.clone())) {
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

    // -------------------------------------------------------------------------------------------//
    // ---------------------------- CLAUSE LEARNING ----------------------------------------------//
    // -------------------------------------------------------------------------------------------//

    /// Returns true iff the given `position` (index) in the trail `prop_queue` is an unique
    /// implication point (UIP). A position is an uip if:
    /// - it is a decision.
    /// - it is the last marked literal before a decision.
    pub fn is_uip(&self, position: usize) -> bool {
        let literal = self.trail.prop_queue[position];

        if self.trail.is_decision(literal) {
            return true;
        }

        if !self.flags[literal].is_set(Flag::IsMarked) {
            return false;
        }

        for iter in (self.trail.forced..position).rev() {
            let iter_literal= self.trail.prop_queue[iter];

            if self.flags[iter_literal].is_set(Flag::IsMarked) {
                return false;
            }
            if self.trail.is_decision(iter_literal) {
                return true;
            }
        }

        return false;
    }
}

// -----------------------------------------------------------------------------------------------
/// # Valuation
/// This struct encapsulates the idea of an assignment of Variables to Bool values.
// -----------------------------------------------------------------------------------------------

#[derive(Debug)]
pub struct VariableState {
    pub value : Bool,
    pub reason: Option<Reason>
}

impl VariableState {
    pub fn default() -> VariableState {
        VariableState{value: Bool::Undef, reason: None}
    }
}

#[derive(Debug)]
pub struct Valuation ( VarIdxVec<VariableState> );

impl Valuation {

    pub fn new(nb_vars: usize) -> Valuation {
        let mut valuation= Valuation(VarIdxVec::with_capacity(nb_vars));
        // initialize the items
        for _ in 0..nb_vars {
            valuation.0.push(VariableState::default() );
        }
        return valuation;
    }

    pub fn get_value(&self, l: Literal) -> Bool {
        let value = self.0[l.var()].value;

        match l.sign() {
            Sign::Positive =>  value,
            Sign::Negative => !value
        }
    }

    pub fn set_value(&mut self, l: Literal, value : Bool, reason: Option<Reason>) {
        self.0[l.var()] = match l.sign() {
            Sign::Positive => VariableState{value:  value, reason},
            Sign::Negative => VariableState{value: !value, reason}
        }
    }

    pub fn is_undef(&self, l: Literal) -> bool {
        self.0[l.var()].value == Bool::Undef
    }
    pub fn is_true (&self, l: Literal) -> bool {
        match l.sign() {
            Sign::Positive => self.0[l.var()].value == Bool::True,
            Sign::Negative => self.0[l.var()].value == Bool::False,
        }
    }
    pub fn is_false(&self, l: Literal) -> bool {
        match l.sign() {
            Sign::Positive => self.0[l.var()].value == Bool::False,
            Sign::Negative => self.0[l.var()].value == Bool::True,
        }
    }
}

impl Deref for Valuation {
    type Target = VarIdxVec<VariableState>;

    #[inline]
    fn deref(&self) -> &VarIdxVec<VariableState> {
        &self.0
    }
}

impl DerefMut for Valuation {
    #[inline]
    fn deref_mut(&mut self) -> &mut VarIdxVec<VariableState> {
        &mut self.0
    }
}

// -----------------------------------------------------------------------------------------------
/// # Trail
/// The structure that memorizes the state and order in which literals have been assigned
// -----------------------------------------------------------------------------------------------
#[derive(Debug)]
pub struct Trail {
    pub valuation  : Valuation,
    pub prop_queue : Vec<Literal>,
    pub forced     : usize,
    pub propagated : usize
}

impl Trail {
    /// Assigns a given literal to True. That is to say, it assigns a value to the given literal
    /// in the Valuation and it enqueues the negation of the literal on the propagation queue
    ///
    /// # Note
    /// We always push the *negation* of the assigned literal on the stack
    pub fn assign(&mut self, lit: Literal, reason: Option<Reason>) -> Result<(), ()> {
        match self.valuation.get_value(lit) {
            Bool::True  => Ok(()),
            Bool::False => Err(()),
            Bool::Undef => {
                self.valuation.set_value(lit, Bool::True, reason);
                self.prop_queue.push(!lit);
                Ok(())
            }
        }
    }

    pub fn is_decision(&self, lit : Literal) -> bool {
        self.valuation[lit.var()].reason.is_none()
    }
}

#[cfg(test)]
mod test_solver {
    use super::*;
    use super::super::*;

    #[test]
    fn propagate_processes_everything_until_a_fixed_point_is_reached(){
        let mut solver = Solver::new(3);

        // initialize the constraint database
        solver.add_problem_clause(vec![1, -2, -3]);
        solver.add_problem_clause(vec![2, -3]);
        solver.add_problem_clause(vec![3]);

        // start the test (for real !)
        solver.trail.assign(Literal::from(3), None).expect("3 should be assignable");

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
        solver.add_problem_clause(vec![ 1, -2, -3]);
        solver.add_problem_clause(vec![ 2, -3]);
        solver.add_problem_clause(vec![ 3]);
        solver.add_problem_clause(vec![-2]);

        // start the test (for real !)
        solver.trail.assign(Literal::from( 3), None).expect(" 3 should be assignable");
        // if I propagated here, then -2 shouldn't be assignable anymore
        solver.trail.assign(Literal::from(-2), None).expect("-2 should be assignable");

        let conflict = solver.propagate();
        assert_eq!("Some(Alias(Some(Clause([Literal(2), Literal(-3)]))))", format!("{:?}", conflict));
        assert_eq!(solver.trail.prop_queue, vec![lit(-3), lit(2)])
    }

    #[test]
    fn propagate_finds_a_non_trivial_conflict(){
        /*-
         * a ------------------------------------/--- c
         *                                      /
         *     /------- e ---- f --- -b --- -h +
         *    /                    /           \
         * d /-- g ---------------/             \--- -c
         *
         */
        let mut solver = Solver::new(8);
        solver.add_problem_clause(vec![ 1,-8, 3]); // c0
        solver.add_problem_clause(vec![ 1, 4,-5]); // c1
        solver.add_problem_clause(vec![ 5,-6, 7]); // c2
        solver.add_problem_clause(vec![ 6, 2, 7]); // c3
        solver.add_problem_clause(vec![ 4,-7]);    // c4
        solver.add_problem_clause(vec![-2, 8]);    // c5
        solver.add_problem_clause(vec![-8,-3]);    // c6

        assert_eq!(Ok(()), solver.trail.assign(lit(-1), None));
        assert_eq!(Ok(()), solver.trail.assign(lit(-4), None));

        let conflict = solver.propagate();
        assert!(conflict.is_some());
        assert_eq!(format!("{:?}", solver.constraints[6].alias()), format!("{:?}", conflict.unwrap()));
    }

    // isUIP must be true when the literal is a decision
    #[test]
    fn is_uip_must_be_true_when_literal_is_a_decision() {
        let mut solver = Solver::new(8);

        solver.trail.assign(lit(2), None).expect("2 must be assignable");
        solver.trail.assign(lit(4), None).expect("4 must be assignable");
        solver.trail.assign(lit(8), None).expect("8 must be assignable");

        assert!(solver.is_uip(0));
        assert!(solver.is_uip(1));
        assert!(solver.is_uip(2));
    }

    // isUIP must be true when there is no other marked literal before next decision
    #[test]
    fn is_uip_must_be_true_when_there_is_no_other_marked_literal_before_next_decision(){
        /*-
         * a ------------------------------------/--- c
         *                                      /
         *     /------- e ---- f --- -b --- -h +
         *    /                    /           \
         * d /-- g ---------------/             \--- -c
         *
         */
        let mut solver = Solver::new(8);
        solver.add_problem_clause(vec![ 1,-8, 3]); // c0
        solver.add_problem_clause(vec![ 1, 4,-5]); // c1
        solver.add_problem_clause(vec![ 5,-6, 7]); // c2
        solver.add_problem_clause(vec![ 6, 2, 7]); // c3
        solver.add_problem_clause(vec![ 4,-7]);    // c4
        solver.add_problem_clause(vec![-2, 8]);    // c5
        solver.add_problem_clause(vec![-8,-3]);    // c6

        assert_eq!(Ok(()), solver.trail.assign(lit(-1), None));
        assert_eq!(Ok(()), solver.trail.assign(lit(-4), None));

        let conflict = solver.propagate();

        // FIXME: find first uip !!

        assert!(solver.is_uip(6))
    }

}