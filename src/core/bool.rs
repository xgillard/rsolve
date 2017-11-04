use std::ops::*;
use super::*;

// -----------------------------------------------------------------------------------------------
/// # Bool
/// This is the representation of a boolean value in a tri-valued logic. It can be either True,
/// False or Undefined
// -----------------------------------------------------------------------------------------------
#[derive(Eq, Clone, Copy, Debug)]
pub enum Bool { True, False, Undef }

impl Bool {
    #[inline]
    pub fn to_i8(&self) -> i8 {
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
/// # Unit Tests
// -----------------------------------------------------------------------------------------------
#[cfg(test)]
mod tests {
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