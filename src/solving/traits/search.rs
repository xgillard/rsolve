// -----------------------------------------------------------------------------------------------
/// # Search
/// This trait specifies the public interface of a solver. So far it is very scarce (only solve
/// method enforced) but when the solver will go incremental, it should grow.
// -----------------------------------------------------------------------------------------------
pub trait Search {
    /// This is the core method of the solver, it determines the satisfiability of the
    /// problem through a CDCL based solving.
    ///
    /// # Return Value
    /// true if there exist an assignment satisfying the given cnf problem.
    /// false if there exists no such assignment.
    ///
    /// # Note
    /// The cnf problem is not given as an argument of this method. It means that the search needs
    /// to -somehow- have an access to a clause database, propagator, etc.. and that these need to
    /// all be pre configured before calling solve. (Otherwise, a vacuously true answer is to be
    /// expected).
    ///
    fn solve(&mut self) -> bool;
}