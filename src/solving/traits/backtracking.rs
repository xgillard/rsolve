// -----------------------------------------------------------------------------------------------
/// # Backtracking
/// This trait specifies the interface of a solver must fulfill in order to backtrack wrong choices
/// that have been made earlier.
// -----------------------------------------------------------------------------------------------
pub trait Backtracking {
    /// Rolls back the search up to the given position.
    fn rollback(&mut self, until : usize);
}