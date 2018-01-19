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
    lbd: u32,
    /// This flag indicates whether or not the LBD of this clause has 'recently' been updated. That
    /// is to say, it tells whether or not the LBD of this clause has been improved since the last
    /// round of database reduction. This indication is helpful in the sense that it helps protecting
    /// against deletion the clauses that have recently been of interest.
    lbd_recently_updated: bool,
    /// This number is a hash (aka _signature_ ) of the clause. It is useful to implement a fast
    /// check to test equality between two clauses. Computing this hash should not require sorting
    /// the clause.
    pub hash: u64
}

impl Clause {
    /// Creates a new clause from its terms
    pub fn new(terms: Vec<Literal>, is_learned: bool) -> Clause {
        let mut clause = Clause{
            literals: terms,
            is_learned,
            lbd : u32::max_value(),
            lbd_recently_updated: false,
            hash: 0
        };

        clause.literals.shrink_to_fit();
        clause.rehash();

        return clause;
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
        let literals = &mut self.literals;

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

    pub fn is_lbd_recently_updated(&self) -> bool {
        self.lbd_recently_updated
    }
    pub fn set_lbd_recently_updated(&mut self, updated: bool) {
        self.lbd_recently_updated = updated;
    }

    /// This function recomputes the hash of the function and returns it. It *must* be called
    /// whenever a literal is added (unlikely) or removed (very likely) from a clause.
    pub fn rehash(&mut self) {
        self.hash = 0;
        for l in self.literals.iter() { self.hash |= l.hash_code(); }
    }

    /// This function tells whether or not `self` subsumes `other`.
    /// That is to say, this function returns true iff self is a subset of other.
    pub fn subsumes(&self, other: &Clause) -> bool {
        if self.len() > other.len() {
            return false;
        }
        if (self.hash & other.hash) != self.hash {
            return false;
        }

        let mut sv = self.literals.clone();
        let mut ov = other.literals.clone();
        sv.sort_unstable_by_key(|x| x.to_isize());
        ov.sort_unstable_by_key(|x| x.to_isize());

        let mut i = 0;
        let mut j = 0;

        while i < sv.len() && j < ov.len() {
            if sv[i] == ov[j] {
                i += 1;
            }
            j += 1;
        }

        // when the last item of sv was found in ov, i has been incremented !
        return i == sv.len();
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

    #[test]
    fn equal_clauses_should_have_the_same_hash() {
        let c1 = Clause::new(vec![lit(1), lit(2), lit(3)], true);
        let c2 = Clause::new(vec![lit(1), lit(2), lit(3)], true);

        assert_eq!(c1.hash, c2.hash)
    }

    #[test]
    fn equal_clauses_should_have_the_same_hash_even_if_they_are_shuffled() {
        let c1 = Clause::new(vec![lit(1), lit(2), lit(3)], true);
        let c2 = Clause::new(vec![lit(3), lit(1), lit(2)], true);

        assert_eq!(c1.hash, c2.hash)
    }

    #[test]
    fn equal_clauses_should_have_the_same_hash_even_if_there_are_duplicate_literals() {
        let c1 = Clause::new(vec![lit(1), lit(2), lit(3)], true);
        let c2 = Clause::new(vec![lit(3), lit(1), lit(2), lit(3)], true);

        assert_eq!(c1.hash, c2.hash)
    }

    #[test]
    fn different_clauses_should_try_not_to_have_the_same_hash() {
        let c1 = Clause::new(vec![lit(1), lit(2), lit(3)], true);
        let c2 = Clause::new(vec![lit(1), lit(-2), lit(3)], true);

        assert_ne!(c1.hash, c2.hash)
    }

    #[test]
    fn subsuming_clauses_should_not_to_have_the_same_hash() {
        let subsumed = Clause::new(vec![lit(1), lit(2), lit(3)], true);
        let subsuming = Clause::new(vec![lit(1), lit(3)], true);

        assert_ne!(subsumed.hash, subsuming.hash)
    }

    #[test]
    fn hash_can_help_detecting_subsumption() {
        let subsumed = Clause::new(vec![lit(1), lit(2), lit(3)], true);
        let subsuming = Clause::new(vec![lit(1), lit(3)], true);

        assert_eq!( (subsumed.hash & subsuming.hash), subsuming.hash);
        assert_ne!( (subsumed.hash & subsuming.hash), subsumed.hash );
    }

    #[test]
    fn rehash_should_be_idempotent_on_an_untouched_clause() { // its only a waste of time !
        let mut c1 = Clause::new(vec![lit(1), lit(2), lit(3)], true);
        let c2 = Clause::new(vec![lit(3), lit(1), lit(2)], true);

        assert_eq!(c1.hash, c2.hash);
        c1.rehash();
        assert_eq!(c1.hash, c2.hash)
    }

    #[test]
    fn rehash_should_fix_the_hash_of_a_modified_clause() { // its only a waste of time !
        let mut c1 = Clause::new(vec![lit(1), lit(2), lit(3), lit(4)], true);
        let c2 = Clause::new(vec![lit(3), lit(1), lit(2)], true);

        assert_ne!(c1.hash, c2.hash);
        c1.swap_remove(3); // remove lit(4) but it does not automagically change the hash
        assert_ne!(c1.hash, c2.hash);
        c1.rehash(); // fix it !
        assert_eq!(c1.hash, c2.hash)
    }

    #[test]
    fn subsumes_must_be_false_when_self_is_longer_than_other() {
        let a = Clause::new(vec![lit(1), lit(2), lit(3)], true);
        let b = Clause::new(vec![lit(1), lit(2)], true);

        assert!( !a.subsumes(&b) )
    }
    #[test]
    fn subsumes_must_be_false_when_the_hashes_do_not_agree() {
        let a = Clause::new(vec![lit(1),lit(3)], true);
        let b = Clause::new(vec![lit(1), lit(2)], true);

        assert!( !a.subsumes(&b) )
    }
    #[test]
    fn subsumes_must_be_false_when_there_is_a_collision_but_no_match(){
        let mut a = Clause::new(vec![lit(1), lit(2), lit(3)], true);
        let b = Clause::new(vec![lit(1), lit(2)], true);

        a.hash = b.hash; // simulate a collision

        assert!( !a.subsumes(&b) )
    }
    #[test]
    fn subsumes_must_be_true_when_clauses_match(){
        let a = Clause::new(vec![lit(1), lit(2), lit(3)], true);
        let b = Clause::new(vec![lit(1), lit(2), lit(3)], true);

        assert!( a.subsumes(&b) )
    }
    #[test]
    fn subsumes_must_be_true_when_self_is_a_propser_subset_of_other(){
        let a = Clause::new(vec![lit(1), lit(2), lit(3)], true);
        let b = Clause::new(vec![lit(1), lit(2)], true);

        assert!( b.subsumes(&a) )
    }

    #[test]
    fn can_strengthen() {
        // can be strenghtened and the resolvent would be [1, 3]
        let a = Clause::new(vec![lit(1), lit( 2), lit(3)], true);
        let b = Clause::new(vec![lit(1), lit(-2)], true);

        let mut can_do = false;
        for l in a.literals.iter() {
            can_do |= b.hash & ( a.hash | (!*l).hash_code() ) == b.hash;
        }

        // b can strengthen a
        assert!(can_do);
    }
}