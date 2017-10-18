use std::ops::*;
// This file contains an example demonstration of how to implement a typesafe approach to Variables
// and Literals in Rust. That, while remaining highly performant (newtypes are dropped at
// compilation)

#[allow(non_camel_case_types)]
pub type uint = u32;
#[allow(non_camel_case_types)]
pub type iint = i32;

// -----------------------------------------------------------------------------------------------
// Variable
// -----------------------------------------------------------------------------------------------
#[derive(Clone, Copy, Eq, Debug)]
pub struct Variable(uint);

impl Variable {
    pub fn from(x: uint) -> Variable {
        assert_ne!(x, 0, "Variables must be strictly positive");
        Variable(x)
    }

    #[inline]
    pub fn to_usize(self) -> usize { self.0 as usize }
}

impl PartialEq for Variable {
    fn eq(&self, other : &Variable) -> bool {
        self.0 == other.0
    }
}

// -----------------------------------------------------------------------------------------------
// Literal
// -----------------------------------------------------------------------------------------------
#[derive(Clone, Copy, Eq, Debug)]
pub struct Literal(iint);

pub enum Sign { Positive, Negative }

impl Literal {

    pub fn from(l: iint) -> Literal {
        assert_ne!(l, 0, "Zero is not allowed as a literal identifier");
        Literal(l)
    }

    pub fn from_var(v: Variable, s: Sign) -> Literal {
        match s {
            Sign::Positive => Literal::positive(v),
            Sign::Negative => Literal::negative(v)
        }
    }

    pub fn positive(v: Variable) -> Literal {
        Literal(  v.0 as iint )
    }

    pub fn negative(v: Variable) -> Literal {
        Literal(-(v.0 as iint))
    }

    pub fn var(self) -> Variable {
        Variable(if self.0 > 0 { self.0 } else { -self.0 } as uint)
    }

    pub fn sign(self) -> Sign {
        if self.0 < 0 { Sign::Negative } else { Sign::Positive }
    }

    #[inline]
    pub fn to_isize(self) -> isize { self.0 as isize }
}

impl PartialEq for Literal {
    fn eq(&self, other : &Literal) -> bool {
        self.0 == other.0
    }
}

impl Neg for Literal {
    type Output = Literal;
    fn neg(self) -> Literal {
        Literal(-self.0)
    }
}

impl Not for Literal {
    type Output = Literal;
    fn not(self) -> Literal {
        Literal(-self.0)
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