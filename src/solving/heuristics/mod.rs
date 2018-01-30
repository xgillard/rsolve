use core::*;

/// Abstraction of a variable selection heuristic.
pub trait BranchingHeuristic {
    /// Creates a new VSIDS capable of dealing with `capa` variables.
    fn new(capa: usize) -> Self;

    /// return true iff there is no element left in the heap
    fn is_empty(&self) -> bool;

    /// Updates the variable's score according to the implemented heuristic
    fn bump(&mut self, var: Variable);

    /// (Optional) Ages the score of all the variables to make them appear less relevant
    fn decay(&mut self);

    /// Places the given `var` back in the heap (if not already present)
    ///
    /// # Panics
    /// - if the given variable does not fit in the range [1 .. capa]
    fn push_back(&mut self, var: Variable);

    /// Removes the element with highest score from the heap and returns it.
	///
	/// # Return Value
	/// Returns the element with highest score on the heap.
	///
	/// # Panics
	/// - when one tries to pop an empty heap.
    fn pop_top(&mut self) -> Variable;
}

/// Abstraction of a restart strategy.
pub trait RestartHeuristic {
    /// Tells whether the solver should restart given it has already encountered `nb_conflicts`
    fn should_restart(&self, nb_conflict: usize) -> bool;

    /// Sets the next conflict limit before the next restart
    fn set_next_limit(&mut self);
}

pub mod branching;
pub mod restart;

pub use self::branching::*;
pub use self::restart::*;