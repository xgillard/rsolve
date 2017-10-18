use std::rc::{Rc,Weak};

use super::*;

#[derive(Debug)]
pub struct Variables {
    /// The total number of variables being dealt with in the current propblem instance
    var_max : usize,
    /// The last forced phase of each variable. (index start at 1)
    phase   : Vec<bool>,
    /// The reason for the last assignation
    reason  : Vec<Option<Weak<Clause>>>
}

impl Variables {
    pub fn new(var_max: usize) -> Variables {
        return Variables {
            var_max,
            phase : vec![false; 1+var_max],
            reason: vec![None ; 1+var_max]
        };
    }

    pub fn set_reason(&mut self, var: Variable, reason: &Rc<Clause>) {
        self.reason[var] = Some(Rc::downgrade(reason));
    }

    pub fn get_reason(&self, var: Variable) -> &Option<Weak<Clause>> {
        return &self.reason[var];
    }
}

#[derive(Debug)]
pub struct Clause {
    data: Vec<Literal>
}