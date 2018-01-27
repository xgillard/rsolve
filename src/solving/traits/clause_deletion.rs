use super::*;

// -----------------------------------------------------------------------------------------------
/// # Clause deletion
/// This trait specifies the public interface of a solver able to forget some of the less useful
/// clauses from its database.
///
/// # Bibliographic Reference
/// See for instance: Predicting Learnt Clauses Quality in Modern SAT Solvers (Audemard, Simon).
// -----------------------------------------------------------------------------------------------
pub trait ClauseDeletion {
    /// Tells whether or not it is desireable to reduce the size of the database and forget some
    /// of the less useful clauses
    fn should_reduce_db(&self) -> bool;

    /// Forgets some of the less useful clauses to speed up the propagation process.
    fn reduce_db(&mut self);

    /// Called whenever the clause propagates a literal.
    fn clause_bump(&mut self, c_id: ClauseId);
}