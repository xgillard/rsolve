use std::ops::*;
use std::fmt;
use std::u32;
use super::*;

// -----------------------------------------------------------------------------------------------
/// # Clause
/// Just like variables and literals, clauses are core concepts of a SAT problem. They are the very
/// building blocks of the satisfiability checking problem (when encoded in CNF form).
/// Concretely, a clause is a disjunction of literals, some of which need to be satisfied (else the
/// whole problem is unsat).
///
/// The main responsibility of a clause object is to maintain a list of literals and arrange them
/// to make propagation efficient. This is achieved using the two watched literals scheme. In
/// particular, the Clause class is responsible for making sure that:
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
/// ## Note:
/// The internal field is a Cell<Vec<T>> because we want a clause to be interior mutable.
/// In other word, we dont care if the order of the literals changes as long as we have a
///
// -----------------------------------------------------------------------------------------------
#[derive(Clone)]
pub struct Clause {
    /// This is the actual set of literals composing the clause
    literals: Vec<Literal>,
    /// A flag indicating whether or not this clause originates from the problem definition or if
    /// it was learned during search
    pub is_learned: bool,
    /// This is an heuristic 'quality' score associated with each of the clauses which is used
    /// by the solver's clause management (removal) strategy. It measures the number of propagation
    /// blocks that were necessary for this clause to become falsified.
    /// See `Predicting Learnt Clauses Quality in Modern SAT Solvers.` Audemard, Simon in aaai2009
    /// for the full details about literal block distance.
    lbd: u32

}

impl Clause {
    /// Creates a new clause from its terms
    pub fn new(terms: Vec<Literal>, is_learned: bool) -> Clause {
        Clause{ literals: terms, lbd : u32::max_value(), is_learned }
    }

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
    pub fn find_new_literal(&mut self, watched:Literal, valuation:&Valuation) -> Result<Literal, Literal> {
        let mut literals = &mut self.literals;

        // Make sure that other WL is at position zero. This way, whenever the clause
        // becomes unit, we are certain to respect invariant B.
        if watched == literals[0] { literals.swap(0, 1); }

        // If the clause is already satsified, we don't need to do anything
        if valuation.is_true(literals[0]) { return Ok(watched); }

        for i in 2..literals.len() {
            let lit = literals[i];

            // not False <==> True or Unassigned
            if !valuation.is_false(lit) {
                // enforce invariant A
                literals.swap(1, i);
                // tell that we need to start watching lit
                return Ok(lit);
            }
        }

        // We couldn't find any new literal to watch. Hence the clause is unit (under
        // the current assignment) or conflicting.
        return Err(literals[0]);
    }

    /// Returns the heuristic 'quality' score associated with this clause
    pub fn get_lbd(&self) -> u32 {
        self.lbd
    }
    /// Changes the heuristic 'quality' score associated with this clause
    pub fn set_lbd(&mut self, lbd: u32) {
        self.lbd = lbd;
    }

    /// Returns a DIMACS string representation of this clause
    pub fn to_dimacs(&self) -> String {
        let mut out = String::new();

        for l in self.literals.iter() {
            out.push_str(&format!("{} ", l.to_isize()));
        }
        out.push_str("0");
        return out;
    }
}

impl Deref for Clause {
    type Target = Vec<Literal>;

    #[inline]
    fn deref(&self) -> &Vec<Literal>{
        &self.literals
    }
}
impl DerefMut for Clause{
    #[inline]
    fn deref_mut(&mut self) -> &mut Vec<Literal>{
        &mut self.literals
    }
}

impl fmt::Debug for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Clause({:?})", self.literals )
    }
}

// -----------------------------------------------------------------------------------------------
/// # Unit Tests
/// Note that the tests folder also contain some integration tests in which the clause intervene
// -----------------------------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn find_new_literal_does_nothing_if_the_clause_is_already_sat(){
        let mut valuation= Valuation::new(8);

        valuation.set_value(lit(1), Bool::True);
        valuation.set_value(lit(2), Bool::False);
        valuation.set_value(lit(4), Bool::False);
        valuation.set_value(lit(8), Bool::Undef);

        // create the tested clause
        let mut clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        let watched = Literal::from(2);
        assert_eq!(clause.find_new_literal(watched, &valuation), Ok(Literal::from(2)))
    }

    #[test]
    fn find_new_literal_does_nothing_if_the_clause_is_already_sat_2(){
        let mut valuation= Valuation::new(8);

        valuation.set_value(lit(1), Bool::False);
        valuation.set_value(lit(2), Bool::True);
        valuation.set_value(lit(4), Bool::False);
        valuation.set_value(lit(8), Bool::Undef);

        // create the tested clause
        let mut clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        let watched = Literal::from(1);
        assert_eq!(clause.find_new_literal(watched, &valuation), Ok(Literal::from(1)))
    }

    #[test]
    fn find_new_literal_returns_ok_with_the_first_unassigned(){
        let mut valuation= Valuation::new(8);

        valuation.set_value(lit(1), Bool::False);
        valuation.set_value(lit(2), Bool::False);
        valuation.set_value(lit(4), Bool::Undef);
        valuation.set_value(lit(8), Bool::Undef);

        // create the tested clause
        let mut clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        let watched = Literal::from(1);
        assert_eq!(clause.find_new_literal(watched, &valuation), Ok(Literal::from(4)))
    }

    #[test]
    fn find_new_literal_does_not_pick_one_of_the_wl_as_new_wl(){
        let mut valuation= Valuation::new(8);

        valuation.set_value(lit(1), Bool::False);
        valuation.set_value(lit(2), Bool::Undef);
        valuation.set_value(lit(4), Bool::False);
        valuation.set_value(lit(8), Bool::Undef);

        // create the tested clause
        let mut clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        let watched = Literal::from(1);
        assert_eq!(clause.find_new_literal(watched, &valuation), Ok(Literal::from(8)))
    }

    #[test]
    fn find_new_literal_returns_ok_with_first_satisfied_literal_when_one_is_found_1(){
        let mut valuation= Valuation::new(8);

        valuation.set_value(lit(1), Bool::False);
        valuation.set_value(lit(2), Bool::Undef);
        valuation.set_value(lit(4), Bool::True);
        valuation.set_value(lit(8), Bool::Undef);

        // create the tested clause
        let mut clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        let watched = Literal::from(1);
        assert_eq!(clause.find_new_literal(watched, &valuation), Ok(Literal::from(4)))
    }

    #[test]
    fn find_new_literal_returns_ok_with_first_satisfied_literal_when_one_is_found_2(){
        let mut valuation= Valuation::new(8);

        valuation.set_value(lit(1), Bool::False);
        valuation.set_value(lit(2), Bool::Undef);
        valuation.set_value(lit(4), Bool::False);
        valuation.set_value(lit(8), Bool::True);

        // create the tested clause
        let mut clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        let watched = Literal::from(1);
        assert_eq!(clause.find_new_literal(watched, &valuation), Ok(Literal::from(8)))
    }

    #[test]
    fn find_new_literal_tells_what_literal_to_assert_when_it_fails_to_find_a_new_lit(){
        let mut valuation= Valuation::new(8);

        valuation.set_value(lit(1), Bool::False);
        valuation.set_value(lit(2), Bool::Undef);
        valuation.set_value(lit(4), Bool::False);
        valuation.set_value(lit(8), Bool::False);

        // create the tested clause
        let mut clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        let watched = Literal::from(1);
        assert_eq!(clause.find_new_literal(watched, &valuation), Err(Literal::from(2)))
    }
}