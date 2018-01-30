use core::*;
use solving::heuristics::BranchingHeuristic;

/// This is the implementation of a very naive (and basic) variable selection heuristic.
/// It isn't smart nor effective, and you probably don't want to use it except for the comparison.
pub struct NaiveVariableSelection {
    available: Vec<Variable>
}

impl BranchingHeuristic for NaiveVariableSelection {
    /// Creates a new heuristic capable of dealing with `capa` variables.
    fn new(capa: usize) -> Self {
        let mut ret = NaiveVariableSelection {available: Vec::with_capacity(capa) };

        for i in 1..(1+capa) {
            ret.available.push(Variable::from(i))
        }

        return ret;
    }

    /// return true iff there is no element left in the heap
    fn is_empty(&self) -> bool { self.available.is_empty() }

    #[allow(unused_variables)]
    /// (Optional) Updates the variable's score according to the implemented heuristic
    fn bump(&mut self, var: Variable) {}

    /// (Optional) Ages the score of all the variables to make them appear less relevant
    fn decay(&mut self) {}

    /// Places the given `var` back in the heap (if not already present)
    ///
    /// # Panics
    /// - if the given variable does not fit in the range [1 .. capa]
    fn push_back(&mut self, var: Variable) {
        if self.available.iter().find(|v| **v == var).is_none() {
            self.available.push(var);
        }
    }

    /// Removes the element with highest score from the heap and returns it.
	///
	/// # Return Value
	/// Returns the element with highest score on the heap.
	///
	/// # Panics
	/// - when one tries to pop an empty heap.
    fn pop_top(&mut self) -> Variable {
        self.available.pop().unwrap()
    }
}