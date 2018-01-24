use super::*;

use std::convert::From;

// -----------------------------------------------------------------------------------------------
/// # Variable
/// This is as a basic variable as you can imagine. This type simply wraps an unsigned integer and
/// behaves like it. (Copy iso move, equals)
// -----------------------------------------------------------------------------------------------
#[derive(Clone, Copy, Eq, Debug)]
pub struct Variable(uint);

impl From<usize> for Variable {
    #[inline]
    fn from(v : usize) -> Variable {
        assert_ne!(v, 0, "Variables must be strictly positive");
        Variable(v as uint)
    }
}
impl From<u32> for Variable {
    #[inline]
    fn from(v : u32) -> Variable {
        assert_ne!(v, 0, "Variables must be strictly positive");
        Variable(v as uint)
    }
}

impl From<Variable> for usize {
    #[inline]
    fn from(v : Variable) -> usize { v.0 as usize }
}
impl From<Variable> for u32 {
    #[inline]
    fn from(v : Variable) -> u32 { v.0 }
}

/// Because variables have an identity (besides their memory location), the Variable type implements
/// Eq and PartialEq to allow comparison with the == operator
impl PartialEq for Variable {
    fn eq(&self, other : &Variable) -> bool {
        self.0 == other.0
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
    fn from_should_fail_on_zero() {
        assert_eq!("Variable(0)", format!("{:?}", var(0)));
    }

    // negatives are caught by the compiler

    #[test]
    fn from_should_work_on_positive_number() {
        assert_eq!("Variable(42)", format!("{:?}", var(42)));
    }

    #[test]
    fn test_equals_is_true_for_same_values() {
        assert_eq!(var(42), var(42));
    }
    #[test]
    fn test_equals_is_false_for_different_values() {
        assert_ne!(var(5), var(42));
    }
}