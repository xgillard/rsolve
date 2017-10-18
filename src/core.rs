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