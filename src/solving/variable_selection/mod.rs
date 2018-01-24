use core::*;

/// Abstraction of a variable selection heuristic.
pub trait VariableSelection {
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

mod naive;
pub use self::naive::NaiveVariableSelection;

mod vsids;
pub use self::vsids::VSIDS;