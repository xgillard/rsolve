use core::*;
use super::*;

// -----------------------------------------------------------------------------------------------
/// # Clause Database
/// This trait communicates the intent that the implementer is the owner of the clauses composing
/// the problem.
// -----------------------------------------------------------------------------------------------
pub trait ClauseDatabase {
    /// Adds a problem clause to the database.
    ///
    /// # Return Value
    /// This function returns a Result (Ok, Err) with the id of the clause that has been added.
    /// However, when it is decided not to add the clause to database, Ok(CLAUSE_ELIDED) is returned.
    fn add_problem_clause(&mut self, c : &mut Vec<iint>) -> Result<ClauseId, ()>;

    /// Adds a learned clause to the database.
    ///
    /// # Return Value
    /// This function returns a Result (Ok, Err) with the id of the clause that has been added.
    /// However, when it is decided not to add the clause to database, Ok(CLAUSE_ELIDED) is returned.
    fn add_learned_clause(&mut self, c :Vec<Literal>) -> Result<ClauseId, ()>;

    /// Removes the clause identified by `c_id` from the database.
    fn remove_clause(&mut self, c_id: ClauseId);

    /// Proceed to the deletion of a set of clauses in the database.
    /// All the clauses identified by an id in the remove_agenda will be removed.
    fn remove_all(&mut self, remove_agenda: &mut [ClauseId]);
}