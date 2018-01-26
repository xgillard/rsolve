use core::*;
use super::*;

// -----------------------------------------------------------------------------------------------
/// # Clause Database
/// This trait communicates the intent that the implementer is the owner of the clauses composing
/// the problem.
// -----------------------------------------------------------------------------------------------
pub trait ClauseDatabase {
    /// Adds a new clause to the database.
    ///
    /// # Return Value
    /// It returns Ok(clause_id) when the clause could be added to the database and Err(()) when
    /// it couldn't. In the former case, `clause_id` is the identifier of the clause that has just
    /// been added to the database or the constant CLAUSE_ELIDED which is used to mean that the
    /// clause was not explicitly encoded but was implicitly represented instead (this is ie useful
    /// for unit clauses). In the event where the addition of the clause would make the whole
    /// problem unsat, this method returns Err(()).
    fn add_clause(&mut self, c: Clause) -> Result<ClauseId, ()>;

    /// Removes the clause identified by `c_id` from the database.
    fn remove_clause(&mut self, c_id: ClauseId);

    /// Returns a reference to the underlying set of clauses.
    fn get_clauses    (&self)     -> &    [Clause];

    /// Returns a mutable reference to the underlying set of clauses
    fn get_clauses_mut(&mut self) -> &mut Vec<Clause>;

    /// Returns a reference to the clause identified by `c_id`
    fn get_clause    (&self,     c_id: ClauseId) -> &Clause     { &    self.get_clauses    ()[c_id]}

    /// Returns a mutable reference to the clause identified by `c_id`
    fn get_clause_mut(&mut self, c_id: ClauseId) -> &mut Clause { &mut self.get_clauses_mut()[c_id]}
}