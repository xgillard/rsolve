use std::ops::*;
use super::*;

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
        Literal(  u32::from(v) as iint )
    }

    /// Returns the negative literal associated with the given variable
    pub fn negative(v: Variable) -> Literal {
        Literal(-(u32::from(v) as iint))
    }

    /// Return the variable associated with the given literal
    pub fn var(self) -> Variable {
        var(if self.0 > 0 { self.0 } else { -self.0 } as uint)
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
/// # Unit Tests
// -----------------------------------------------------------------------------------------------
#[cfg(test)]
mod tests {
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
        assert_eq!("Literal(1)", format!("{:?}", Literal::from_var(var(1), Sign::Positive)));
        assert_eq!("Literal(-1)", format!("{:?}", Literal::from_var(var(1), Sign::Negative)));
    }
    #[test]
    fn positive_builds_positive_lit(){
        assert_eq!("Literal(1)", format!("{:?}", Literal::positive(var(1))));
    }
    #[test]
    fn negative_builds_negative_lit(){
        assert_eq!("Literal(-1)", format!("{:?}", Literal::negative(var(1))));
    }
    #[test]
    fn var_returns_the_original_var(){
        let v = var(42);

        assert_eq!(v, Literal::positive(v).var());
        assert_eq!(v, Literal::negative(v).var());
    }
    #[test]
    fn sign_is_positive_for_positive_lits(){
        let v = var(42);

        if let Sign::Positive = Literal::positive(v).sign() {
            assert!(true);
        } else {
            panic!("Should have been positive")
        }
    }
    #[test]
    fn sign_is_negative_for_negative_lits(){
        let v = var(42);

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
        let b = Literal::negative(var(1));
        let c = Literal::from_var(var(1), Sign::Negative);

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
        let b = Literal::positive(var(1));
        let c = Literal::from_var(var(1), Sign::Positive);

        assert_eq!(a, --a);
        assert_eq!(a, -b);
        assert_eq!(a, -c);
    }
    #[test]
    fn test_not(){
        let a = Literal::from(-1);
        let b = Literal::positive(var(1));
        let c = Literal::from_var(var(1), Sign::Positive);

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