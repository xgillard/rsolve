use std::ops::*;

use solver::*;

// This file contains an example demonstration of how to implement a typesafe approach to Variables
// and Literals in Rust. That, while remaining highly performant (newtypes are dropped at
// compilation)

#[allow(non_camel_case_types)]
pub type uint = u32;
#[allow(non_camel_case_types)]
pub type iint = i32;

#[derive(Clone, Copy, Debug)]
/// This enum trivially encapsulates the polarity (aka the sign) of a boolean variable
pub enum Sign { Positive, Negative }

// -----------------------------------------------------------------------------------------------
/// # Bool
/// This is the representation of a boolean value in a tri-valued logic. It can be either True,
/// False or Undefined
// -----------------------------------------------------------------------------------------------
#[derive(Eq, Clone, Copy, Debug)]
pub enum Bool { True, False, Undef }

impl Bool {
    #[inline]
    fn to_i8(&self) -> i8 {
        match *self {
            Bool::True =>  1,
            Bool::False=> -1,
            Bool::Undef=>  0
        }
    }
}

impl PartialEq for Bool {
    fn eq(&self, other: &Bool) -> bool { self.to_i8() == other.to_i8() }
}

impl Not for Bool {
    type Output = Bool;

    #[inline]
    fn not(self) -> Bool {
        match self {
            Bool::True  => Bool::False,
            Bool::False => Bool::True,
            Bool::Undef => Bool::Undef
        }
    }
}

// -----------------------------------------------------------------------------------------------
/// # Variable
/// This is as a basic variable as you can imagine. This type simply wraps an unsigned integer and
/// behaves like it. (Copy iso move, equals)
// -----------------------------------------------------------------------------------------------
#[derive(Clone, Copy, Eq, Debug)]
pub struct Variable(uint);

impl Variable {
    /// Creates a Variable based on its numeric identifier
    pub fn from(x: uint) -> Variable {
        assert_ne!(x, 0, "Variables must be strictly positive");
        Variable(x)
    }

    #[inline]
    /// Returns the numeric identifier of the variable
    pub fn to_usize(self) -> usize { self.0 as usize }
}

/// Because variables have an identity (besides their memory location), the Variable type implements
/// Eq and PartialEq to allow comparison with the == operator
impl PartialEq for Variable {
    fn eq(&self, other : &Variable) -> bool {
        self.0 == other.0
    }
}

// -----------------------------------------------------------------------------------------------
/// # Literal
/// In the same vein as the Variable type, Literal is a thin (but type safe) wrapper around a
/// signed number that represents a literal.
// -----------------------------------------------------------------------------------------------
#[derive(Clone, Copy, Eq, Debug)]
pub struct Literal(iint);

impl Literal {
    /// Creates a Literal based on its numeric (signed) representation.
    pub fn from(l: iint) -> Literal {
        assert_ne!(l, 0, "Zero is not allowed as a literal identifier");
        Literal(l)
    }

    /// Creates a Literal based on a variable and a sign (corresponds more closely to the
    /// theoretical definition of a literal)
    pub fn from_var(v: Variable, s: Sign) -> Literal {
        match s {
            Sign::Positive => Literal::positive(v),
            Sign::Negative => Literal::negative(v)
        }
    }

    /// Returns the positive literal associated with the given variable
    pub fn positive(v: Variable) -> Literal {
        Literal(  v.0 as iint )
    }

    /// Returns the negative literal associated with the given variable
    pub fn negative(v: Variable) -> Literal {
        Literal(-(v.0 as iint))
    }

    /// Return the variable associated with the given literal
    pub fn var(self) -> Variable {
        Variable(if self.0 > 0 { self.0 } else { -self.0 } as uint)
    }

    /// Returns the sign of the given literal
    pub fn sign(self) -> Sign {
        if self.0 < 0 { Sign::Negative } else { Sign::Positive }
    }

    #[inline]
    /// Returns the numeric identifier of the literal
    pub fn to_isize(self) -> isize { self.0 as isize }
}

/// Because literals have an identity (besides their memory location), the Literal type implements
/// Eq and PartialEq to allow comparison with the == operator
impl PartialEq for Literal {
    fn eq(&self, other : &Literal) -> bool {
        self.0 == other.0
    }
}

/// For the sake of convenience, the Literal type implements the Neg and Not traits so that a
/// literal `x` can be simply negated using the `!x` and `-x` syntaxes
impl Neg for Literal {
    type Output = Literal;
    fn neg(self) -> Literal {
        Literal(-self.0)
    }
}

/// For the sake of convenience, the Literal type implements the Neg and Not traits so that a
/// literal `x` can be simply negated using the `!x` and `-x` syntaxes
impl Not for Literal {
    type Output = Literal;
    fn not(self) -> Literal {
        Literal(-self.0)
    }
}

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
#[derive(Debug, Clone)]
pub struct Clause(Vec<Literal>);

impl Clause {
    /// Creates a new clause from its terms
    pub fn new(terms: Vec<Literal>) -> Clause {
        Clause(terms)
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
        let mut literals = &mut self.0;

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
}

// -----------------------------------------------------------------------------------------------
// ------------------------------------- TESTS ---------------------------------------------------
// -----------------------------------------------------------------------------------------------

#[cfg(test)]
mod test_bool {
    use super::*;

    #[test]
    fn to_i8(){
        assert_eq!(-1, Bool::False.to_i8());
        assert_eq!( 1, Bool::True .to_i8());
        assert_eq!( 0, Bool::Undef.to_i8());
    }

    #[test]
    fn eq() {
        assert_eq!(Bool::True , Bool::True );
        assert_ne!(Bool::True , Bool::False);
        assert_ne!(Bool::True , Bool::Undef);

        assert_eq!(Bool::False, Bool::False );
        assert_ne!(Bool::False, Bool::True );
        assert_ne!(Bool::False, Bool::Undef);

        assert_eq!(Bool::Undef, Bool::Undef );
        assert_ne!(Bool::Undef, Bool::True );
        assert_ne!(Bool::Undef, Bool::False);
    }

    #[test]
    fn not(){
        assert_eq!(! Bool::True , Bool::False);
        assert_eq!(! Bool::False, Bool::True );
        assert_eq!(! Bool::Undef, Bool::Undef);
    }
}

#[cfg(test)]
mod test_variable {
    use super::*;

    #[test]
    #[should_panic]
    fn from_should_fail_on_zero() {
        assert_eq!("Variable(0)", format!("{:?}", Variable::from(0)));
    }

    // negatives are caught by the compiler

    #[test]
    fn from_should_work_on_positive_number() {
        assert_eq!("Variable(42)", format!("{:?}", Variable::from(42)));
    }

    #[test]
    fn to_usize_should_return_raw_value() {
        assert_eq!(42, Variable::from(42).to_usize());
    }

    #[test]
    fn test_equals_is_true_for_same_values() {
        assert_eq!(Variable(42), Variable::from(42));
    }
    #[test]
    fn test_equals_is_false_for_different_values() {
        assert_ne!(Variable::from(5), Variable::from(42));
    }
}

#[cfg(test)]
mod test_literal {
    use super::*;

    #[test]
    #[should_panic]
    fn constructor_fails_for_zero(){
        Literal::from(0);
    }

    #[test]
    fn constructor_work_for_positive(){
        assert_eq!("Literal(1)", format!("{:?}", Literal::from(1)));
    }
    #[test]
    fn constructor_work_for_negative(){
        assert_eq!("Literal(-1)", format!("{:?}", Literal::from(-1)));
    }
    #[test]
    fn constructor_work_for_var(){
        assert_eq!("Literal(1)", format!("{:?}", Literal::from_var(Variable::from(1), Sign::Positive)));
        assert_eq!("Literal(-1)", format!("{:?}", Literal::from_var(Variable::from(1), Sign::Negative)));
    }
    #[test]
    fn positive_builds_positive_lit(){
        assert_eq!("Literal(1)", format!("{:?}", Literal::positive(Variable::from(1))));
    }
    #[test]
    fn negative_builds_negative_lit(){
        assert_eq!("Literal(-1)", format!("{:?}", Literal::negative(Variable::from(1))));
    }
    #[test]
    fn var_returns_the_original_var(){
        let v = Variable::from(42);

        assert_eq!(v, Literal::positive(v).var());
        assert_eq!(v, Literal::negative(v).var());
    }
    #[test]
    fn sign_is_positive_for_positive_lits(){
        let v = Variable::from(42);

        if let Sign::Positive = Literal::positive(v).sign() {
            assert!(true);
        } else {
            panic!("Should have been positive")
        }
    }
    #[test]
    fn sign_is_negative_for_negative_lits(){
        let v = Variable::from(42);

        if let Sign::Negative = Literal::negative(v).sign() {
            assert!(true);
        } else {
            panic!("Should have been negative")
        }
    }
    #[test]
    fn to_isize_should_return_raw_value() {
        assert_eq!(-42, Literal::from(-42).to_isize());
    }

    #[test]
    fn test_equality() {
        let a = Literal::from(-1);
        let b = Literal::negative(Variable::from(1));
        let c = Literal::from_var(Variable::from(1), Sign::Negative);

        // reflexive
        assert_eq!(a, a);
        // transitive
        assert_eq!(a, b);
        assert_eq!(b, c);
        assert_eq!(a, c);
        // symmetric
        assert_eq!(a, b);
        assert_eq!(b, a);
    }

    #[test]
    fn test_neg(){
        let a = Literal::from(-1);
        let b = Literal::positive(Variable::from(1));
        let c = Literal::from_var(Variable::from(1), Sign::Positive);

        assert_eq!(a, --a);
        assert_eq!(a, -b);
        assert_eq!(a, -c);
    }
    #[test]
    fn test_not(){
        let a = Literal::from(-1);
        let b = Literal::positive(Variable::from(1));
        let c = Literal::from_var(Variable::from(1), Sign::Positive);

        assert_eq!(a, !!a);
        assert_eq!(a, !b);
        assert_eq!(a, !c);

        assert_ne!(a, !a);
        assert_ne!(a, b);
        assert_ne!(a, c);

        assert_ne!(a, Literal::from(32));
        assert_ne!(a, Literal::from(-32));
    }
}

#[cfg(test)]
mod test_clause {
    use super::*;
    use collections::*;

    #[test]
    fn find_new_literal_does_nothing_if_the_clause_is_already_sat(){
        let mut valuation= Valuation::new(8);

        valuation[Variable::from(1)] = VariableState{ value: Bool::True , reason: None};
        valuation[Variable::from(2)] = VariableState{ value: Bool::False, reason: None};
        valuation[Variable::from(4)] = VariableState{ value: Bool::False, reason: None};
        valuation[Variable::from(8)] = VariableState{ value: Bool::Undef, reason: None};

        // create the tested clause
        let mut clause = Clause(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)]);

        let watched = Literal::from(2);
        assert_eq!(clause.find_new_literal(watched, &valuation), Ok(Literal::from(2)))
    }

    #[test]
    fn find_new_literal_does_nothing_if_the_clause_is_already_sat_2(){
        let mut valuation= Valuation::new(8);

        valuation[Variable::from(1)] = VariableState{ value: Bool::False, reason: None};
        valuation[Variable::from(2)] = VariableState{ value: Bool::True , reason: None};
        valuation[Variable::from(4)] = VariableState{ value: Bool::False, reason: None};
        valuation[Variable::from(8)] = VariableState{ value: Bool::Undef, reason: None};

        // create the tested clause
        let mut clause = Clause(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)]);

        let watched = Literal::from(1);
        assert_eq!(clause.find_new_literal(watched, &valuation), Ok(Literal::from(1)))
    }

    #[test]
    fn find_new_literal_returns_ok_with_the_first_unassigned(){
        let mut valuation= Valuation::new(8);

        valuation[Variable::from(1)] = VariableState{ value: Bool::False, reason: None};
        valuation[Variable::from(2)] = VariableState{ value: Bool::False, reason: None};
        valuation[Variable::from(4)] = VariableState{ value: Bool::Undef, reason: None};
        valuation[Variable::from(8)] = VariableState{ value: Bool::Undef, reason: None};

        // create the tested clause
        let mut clause = Clause(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)]);

        let watched = Literal::from(1);
        assert_eq!(clause.find_new_literal(watched, &valuation), Ok(Literal::from(4)))
    }

    #[test]
    fn find_new_literal_does_not_pick_one_of_the_wl_as_new_wl(){
        let mut valuation= Valuation::new(8);

        valuation[Variable::from(1)] = VariableState{ value: Bool::False, reason: None};
        valuation[Variable::from(2)] = VariableState{ value: Bool::Undef, reason: None};
        valuation[Variable::from(4)] = VariableState{ value: Bool::False, reason: None};
        valuation[Variable::from(8)] = VariableState{ value: Bool::Undef, reason: None};

        // create the tested clause
        let mut clause = Clause(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)]);

        let watched = Literal::from(1);
        assert_eq!(clause.find_new_literal(watched, &valuation), Ok(Literal::from(8)))
    }

    #[test]
    fn find_new_literal_returns_ok_with_first_satisfied_literal_when_one_is_found_1(){
        let mut valuation= Valuation::new(8);

        valuation[Variable::from(1)] = VariableState{ value: Bool::False, reason: None};
        valuation[Variable::from(2)] = VariableState{ value: Bool::Undef, reason: None};
        valuation[Variable::from(4)] = VariableState{ value: Bool::True , reason: None};
        valuation[Variable::from(8)] = VariableState{ value: Bool::Undef, reason: None};

        // create the tested clause
        let mut clause = Clause(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)]);

        let watched = Literal::from(1);
        assert_eq!(clause.find_new_literal(watched, &valuation), Ok(Literal::from(4)))
    }

    #[test]
    fn find_new_literal_returns_ok_with_first_satisfied_literal_when_one_is_found_2(){
        let mut valuation= Valuation::new(8);

        valuation[Variable::from(1)] = VariableState{ value: Bool::False, reason: None};
        valuation[Variable::from(2)] = VariableState{ value: Bool::Undef, reason: None};
        valuation[Variable::from(4)] = VariableState{ value: Bool::False, reason: None};
        valuation[Variable::from(8)] = VariableState{ value: Bool::True , reason: None};

        // create the tested clause
        let mut clause = Clause(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)]);

        let watched = Literal::from(1);
        assert_eq!(clause.find_new_literal(watched, &valuation), Ok(Literal::from(8)))
    }

    #[test]
    fn find_new_literal_tells_what_literal_to_assert_when_it_fails_to_find_a_new_lit(){
        let mut valuation= Valuation::new(8);

        valuation[Variable::from(1)] = VariableState{ value: Bool::False, reason: None};
        valuation[Variable::from(2)] = VariableState{ value: Bool::Undef, reason: None};
        valuation[Variable::from(4)] = VariableState{ value: Bool::False, reason: None};
        valuation[Variable::from(8)] = VariableState{ value: Bool::False, reason: None};

        // create the tested clause
        let mut clause = Clause(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)]);

        let watched = Literal::from(1);
        assert_eq!(clause.find_new_literal(watched, &valuation), Err(Literal::from(2)))
    }
}