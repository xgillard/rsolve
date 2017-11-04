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
    fn to_usize_should_return_raw_value() {
        assert_eq!(42, var(42).to_usize());
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