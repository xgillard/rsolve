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
}