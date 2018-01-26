use core::*;

use super::*;

// -----------------------------------------------------------------------------------------------
/// # Watched Literals
/// This trait encapsulates the Two Watched Literal Scheme proposed in [ZS00, MMZ+01] to speed up
/// the boolean constraint propagation.
///
/// In order to produce an efficient implementation of the Two Watched Literal Scheme,
/// (the default implementations proposed in) this trait arrange the clauses literals so as to
/// maintain the following two invariants:
/// - INVARIANT A: the two watched literals are at index 0 and 1
/// - INVARIANT B: the propagated literal (if there is one) is at index 0.
///
/// The invariant A is specially useful when searching / assigning a new watched
/// literals. It allows us to know immediately what literals are not watched and
/// therefore elligible for watching.
///
/// The invariant B allows us to make an efficient implementation of the
/// conflict analysis (and minimization) procedures. Indeed, it lets us immediately
/// retrieve the antecedant of a propagated literal by starting the iteration
/// at 1 instead of 0.
///
/// [ZS00]   Implementing the davis–putnam method.
///          Hantao Zhang and Mark Stickel.
///          Journal of Automated Reasoning, 24(1-2):277–296, 2000.
///
/// [MMZ+01] Chaff: Engineering an efficient sat solver.
///          Matthew W Moskewicz, Conor F Madigan, Ying Zhao, Lintao Zhang, and Sharad Malik.
///          In Proceedings of the 38th annual Design Automation Conference, pages 530–535. ACM, 2001
// -----------------------------------------------------------------------------------------------
pub trait WatchedLiterals {

    /// Tries to find a new literal that can be watched by the given clause.
    ///
    /// # Return Value
    /// This function returns a Result<Literal, Literal> that mut be interpreted as follows:
    /// - Ok( l ) means that the clause found that l is not satisfied and can therefore be
    ///           watched by the current clause.
    /// - Err(l ) means that no new literals is available to be watched. Hence, l is the last
    ///           literal that can possibly satisfy the clause. If that literal is True or
    ///           Unassigned, then the clause is unit. Otherwise, the clause is conflicting and a
    ///           conflict resolution procedure should be started
    fn find_new_literal(&mut self, c_id: ClauseId, watched: Literal) -> Result<Literal, Literal>;

    /// Activate the given clause. That is to say, it finds two literals to be watched by the clause
    /// and starts watching them.
    ///
    /// In some particular cases, it takes some additional actions. Namely:
    /// - when the clause is detected to be *unit*, it asserts the literal.
    /// - when *a conflict* is detected, it invalidates the state of the solver (it is marked unsat
    ///   for ever).
    ///
    /// # Note
    /// It is assumed that clauses of size 0 and 1 are out of the way and we're certain to be left
    /// only with clauses having at least two literals.
    fn activate_clause(&mut self, c_id : ClauseId);

    /// Deactivate the given clause. That is to say, it removes all watches for the given clause.
    ///
    /// # Note
    /// It is assumed that clauses of size 0 and 1 are out of the way and we're certain to be left
    /// only with clauses having at least two literals.
    fn deactivate_clause(&mut self, c_id: ClauseId);
}