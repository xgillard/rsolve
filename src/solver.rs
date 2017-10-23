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
pub struct Solver {
    trail       : Trail,
    constraints : Vec<Aliasable<Clause>>,
    learned     : Vec<Aliasable<Clause>>,

    // Watchers: vectors of watchers associated with each literal
    watchers    : LitIdxVec<Vec<Watcher>>,
}

impl Solver {
    fn propagate(&mut self) -> Option<Conflict> {
        for i in self.trail.propagated .. self.trail.prop_queue.len() {
            let literal = self.trail.prop_queue[i];
            let conflict = self.propagate_literal(literal);
            if conflict.is_some() {
                return conflict;
            }
        }
        return None;
    }
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
pub struct Valuation {
    pub var_value : VarIdxVec<Bool>
}

impl Valuation {
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