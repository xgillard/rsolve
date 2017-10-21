use core::*;
use collections::*;

pub struct Solver {
    valuation   : Valuation,           // Partial model under construction
    constraints : Vec<Clause>,         // Fixed clauses database, aka original clauses
    learned     : Vec<Clause>,         // Learned clauses database

    watchers    : LitIdxVec<Vec<CId>>, // Watchers: vectors of watchers associated with each literal
}

impl Solver {
    fn propagate(&mut self, lit : Literal) -> Option<Conflict> {
        for i in 0..self.watchers[lit].len() {
            let cid = self.watchers[lit][i];
            let clause = match cid {
                CId::Constraint(offset) => &mut self.constraints[offset],
                CId::Learned   (offset) => &mut self.learned    [offset]
            };

            self.watchers[lit].swap_remove(i);

            match clause.find_new_literal(lit, &self.valuation) {
                Ok (l) => {
                    // l was found, its ok. We only need to start watching it
                    self.watchers[l].push(cid);
                },
                Err(l) => {
                    // No result could be found, so we need to keep on watching lit
                    self.watchers[lit].push(cid);
                    // TODO: assigner si unit ( ==> trail.assign(l, cref, &mut self.valuation)
                    return Some(Conflict(cid)); // or None if the assignment went on well
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
/// # CId (Clause Identifier)
/// A clause identifier basically serves the same purpose as a raw pointer. However, it is somewhat
/// safer than a true pointer because pushing to vec might provoke a reallocation, and hence make
/// the pointer dangling. Note though, that whenever a clause is deleted, the CId might also become
/// dangling. Or worse, it might refer to a wrong clause.
// -----------------------------------------------------------------------------------------------
#[derive(Clone, Copy, Eq, Debug)]
enum CId {
    Constraint(usize),
    Learned(usize)
}

impl CId {
    fn disciminant(&self) -> u8 {
        match *self {
            CId::Constraint(_) => 0,
            CId::Learned   (_) => 1
        }
    }

    fn offset(&self) -> usize {
        match *self {
            CId::Constraint(off) => off,
            CId::Learned   (off) => off
        }
    }
}

impl PartialEq for CId {
    fn eq(&self, other: &CId) -> bool {
        self.disciminant() == other.disciminant() && self.offset() == other.offset()
    }
}

// -----------------------------------------------------------------------------------------------
/// # Conflict
/// A simple algebraic type to explicit the fact that some clause is conflicting
// -----------------------------------------------------------------------------------------------
pub struct Conflict(CId);
