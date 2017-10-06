//! This file contains the implementation of an adaptable heap suitable to implement a VSIDS-like
//! variable ordering
use super::*;
use std::vec::Vec;

/// The variable ordering structure (aka the variable heap)
#[derive(Debug)]
pub struct VariableOrdering {
    /// A binary heap implemented as an array of variables
    heap: Vec<Variable>,
    /// The score associated with each element
    score : Vec<u32>,
    /// The position of each id in the `heap` array
    position: Vec<u32>,
    /// The current size (#elements) in the heap
    size: usize
}

impl VariableOrdering {
    pub fn new(capa: usize) -> VariableOrdering {
        let mut ret = VariableOrdering {
            size    : capa,
            heap    : Vec::with_capacity(1+capa),
            score   : Vec::with_capacity(1+capa),
            position: Vec::with_capacity(1+capa)
        };

        for i in 0..(capa+1) {
            ret.heap    .push(i as Variable);
            ret.position.push(i as u32);
            ret.score   .push(1 as u32);
        }

        return ret;
    }
}

#[cfg(test)]
mod tests {
    use super::VariableOrdering;

    #[test]
    fn test_new() {
        let result = VariableOrdering::new(1);
        eprintln!("{:#?}", result);
    }
}