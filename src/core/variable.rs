use std::ops::*;
use super::*;

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

    #[inline]
    /// Returns the numeric identifier of the variable
    pub fn to_uint (self) -> uint { self.0 }
}

/// Because variables have an identity (besides their memory location), the Variable type implements
/// Eq and PartialEq to allow comparison with the == operator
impl PartialEq for Variable {
    fn eq(&self, other : &Variable) -> bool {
        self.0 == other.0
    }
}
