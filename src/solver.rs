use std::clone::Clone;

use utils::*;
use core::*;
use collections::*;

pub struct Solver {
    valuation   : Valuation,             // Partial model under construction
    constraints : Vec<Aliasable<Clause>>,// Fixed clauses database, aka original clauses
    learned     : Vec<Aliasable<Clause>>,// Learned clauses database

    watchers    : LitIdxVec<Vec<Alias<Clause>>>, // Watchers: vectors of watchers associated with each literal
}

impl Solver {
    fn propagate(&mut self, lit : Literal) -> Option<Conflict> {
        for i in 0..self.watchers[lit].len() {
            let watcher = self.watchers[lit][i].clone();
            self.watchers[lit].swap_remove(i);

            match watcher.get() {
                None         => { /* The clause was deteted, hence the watcher can be ignored */ },
                Some(clause) => {
                    match clause.find_new_literal(lit, &self.valuation) {
                        Ok (l) => {
                            // l was found, its ok. We only need to start watching it
                            self.watchers[l].push(watcher.clone());
                        },
                        Err(l) => {
                            // No result could be found, so we need to keep on watching lit
                            self.watchers[lit].push(watcher.clone());
                            // TODO: assigner si unit ( ==> trail.assign(l, cref, &mut self.valuation)
                            return Some(Conflict(watcher.clone())); // or None if the assignment went on well
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
/// # Conflict
/// A simple algebraic type to explicit the fact that some clause is conflicting
// -----------------------------------------------------------------------------------------------
pub struct Conflict(Alias<Clause>);
