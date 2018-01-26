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
    lbd: u32,
    /// This flag indicates whether or not the LBD of this clause has 'recently' been updated. That
    /// is to say, it tells whether or not the LBD of this clause has been improved since the last
    /// round of database reduction. This indication is helpful in the sense that it helps protecting
    /// against deletion the clauses that have recently been of interest.
    lbd_recently_updated: bool
}

impl Clause {
    /// Creates a new clause from its terms
    pub fn new(terms: Vec<Literal>, is_learned: bool) -> Clause {
        let mut clause = Clause{
            literals: terms,
            is_learned,
            lbd : u32::max_value(),
            lbd_recently_updated: false
        };

        clause.literals.shrink_to_fit();
        return clause;
    }

    /// Returns the heuristic 'quality' score associated with this clause
    pub fn get_lbd(&self) -> u32 {
        self.lbd
    }
    /// Changes the heuristic 'quality' score associated with this clause
    pub fn set_lbd(&mut self, lbd: u32) {
        self.lbd = lbd;
    }

    pub fn is_lbd_recently_updated(&self) -> bool {
        self.lbd_recently_updated
    }
    pub fn set_lbd_recently_updated(&mut self, updated: bool) {
        self.lbd_recently_updated = updated;
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
    fn to_dimacs_must_yield_a_dimacs_string_corresponding_to_the_clause() {
        let clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        assert_eq!("1 2 4 8 0", &clause.to_dimacs());
    }

    #[test]
    fn to_dimacs_must_also_work_for_the_empty_clause() {
        let clause = Clause::new(vec![], false);

        assert_eq!("0", &clause.to_dimacs());
    }

    #[test]
    fn a_clause_can_be_dereferenced_as_an_immutable_vector_of_literals() {
        let clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        assert_eq!(clause.literals, *clause);
    }

    #[test]
    fn a_clause_can_be_dereferenced_as_a_mutable_vector_of_literals() {
        let mut clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        assert_eq!("Clause([Literal(1), Literal(2), Literal(4), Literal(8)])",
                   &format!("{:?}", clause));

        clause.swap(1, 2);

        assert_eq!("Clause([Literal(1), Literal(4), Literal(2), Literal(8)])",
                   &format!("{:?}", clause));
    }
}