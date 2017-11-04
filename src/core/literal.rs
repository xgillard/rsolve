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
        Literal(  v.to_uint() as iint )
    }

    /// Returns the negative literal associated with the given variable
    pub fn negative(v: Variable) -> Literal {
        Literal(-(v.to_uint() as iint))
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