use core::*;
use super::*;

pub trait ClauseDatabase {
    fn add_clause(&mut self, c: Clause) -> Result<ClauseId, ()>;
    fn remove_clause(&mut self, c_id: ClauseId);

    fn get_clauses    (&self)     -> &    [Clause];
    fn get_clauses_mut(&mut self) -> &mut Vec<Clause>;

    fn get_clause    (&self,     c_id: ClauseId) -> &Clause     { &    self.get_clauses    ()[c_id]}
    fn get_clause_mut(&mut self, c_id: ClauseId) -> &mut Clause { &mut self.get_clauses_mut()[c_id]}
}