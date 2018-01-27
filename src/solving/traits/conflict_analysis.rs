use core::*;
use super::*;

// -----------------------------------------------------------------------------------------------
/// # Conflict Analysis
/// This trait specifies the interface of a solver capable of analyzing a conflict (through a
/// backwards BFS traversal of the implication graph) and to derive a new clause from the conflict.
// -----------------------------------------------------------------------------------------------
pub trait ConflictAnalysis {
    /// This method analyzes the conflict to derive a new clause, add it to the database and
    /// rolls back the assignment stack until the moment where the solver has reached a stable
    /// and useful state (from which progress can be made).
    ///
    /// # Note
    /// In the implementation proposed in `Solver`, the conflict clause which is learned is
    /// immediately minimized with the so called recursive minimization technique.
    /// For further reference, please refer to:
    /// * Minimizing Learned Clauses (Sörensson, Biere -- 2009)
    ///
    /// # Return Value
    /// Ok  whenever the conflict could safely be resolved,
    /// Err when the conflict could not be resolved (that is to say, when the problem is
    ///     proven to be UNSAT
    fn resolve_conflict(&mut self, conflict: ClauseId) -> Result<(), ()>;

    /// This method builds and returns a minimized conflict clause.
    ///
	/// `uip` is the position of the 1st uip
    fn build_conflict_clause(&mut self, uip: usize) -> Vec<Literal>;

    /// Finds the position (in the trail) of the first unique implication point
    /// implying the conflict detected because of `conflicting`. Concretely, this
    /// is implemented with a backwards BFS traversal of the implication graph and
    /// each step is an inverse resolution.
    ///
    /// `conflicting` is the id of the clause which was detected to be the reason of the conflict
    /// This function returns the position of the first uip
    fn find_first_uip(&mut self, conflict: ClauseId) -> usize;

    /// Returns true iff the given `position` (index) in the trail is an unique implication point
    /// (UIP). A position is an uip if:
    /// - it is a decision.
    /// - it is the last marked literal before a decision.
    fn is_uip(&self, position: usize) -> bool;

    /// Returns true iff recursive analysis showed `lit` to be implied by other literals
    ///
    /// # Bibliographic reference
    /// For further reference on recursive clause minimization, please refer to
    /// * Minimizing Learned Clauses (Sörensson, Biere -- 2009)
    ///
    fn is_implied(&mut self, lit: Literal) -> bool;

    /// Returns the position (index in the trail) until which the solver should backtrack
    /// to continue searching while incorporating the knowledge gained with learned clause
    /// implying `uip`.
    ///
    /// The returned position corresponds to the index of the *earliest* decision point which
    /// makes the learned clause unit.
    fn find_backjump_point(&self, uip: usize) -> usize;
}