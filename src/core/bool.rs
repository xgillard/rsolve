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