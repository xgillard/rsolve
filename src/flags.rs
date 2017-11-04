use std::string::String;
use std::fmt::{Debug, Formatter, Result};
use std::ops::{BitOr, BitAnd, BitOrAssign, BitAndAssign, BitXor, BitXorAssign};

/// The `Flag` enum is simply a type safe way to constrain the flags that can possibly be set for
/// any given literal.
#[derive(Debug)]
pub enum Flag {
    Clear              =  0, //--> serves to reset all flags
    IsMarked           =  1, //--> used during conflict analysis
    IsImplied          =  2, //--> forced by the ongoing conflict clause
    IsNotImplied       =  4, //--> not forced but effectively analysed
    IsInConflictClause =  8  //--> makes it easy to retrieve the backjump point
}

/// The `Flags` newtype, as its name suggests, serves the point of collecting the various flags that
/// have been turned on for some literals; and to pack these in a single byte.
///
/// For the sake of convenience, most bitwise operations have been implemented on the `Flags` type.
/// For instance:
///   - BitOr  and BitOrAssign   (| and |=)
///   - BitAnd and BitAndAssign  (& and &=)
///   - BitXor and BitXorAssign  (^ and &=)
///
/// Additionally, `Flags` also implements the following traits:
///   - Debug so that its easy to see what flags are set
///   - Clone and Copy so that the compiler knows that `Flags` should be treated like an other basic
///     type (ie an u8)s
#[derive(Clone, Copy)]
pub struct Flags(u8);

impl Flags {
    /// Constructor
    #[inline]
    pub fn new() -> Flags { Flags(Flag::Clear as u8) }

    /// Turn on some given flag _in place_
    #[inline]
    pub fn set(&mut self, f: Flag) { self.0 |= f as u8 }

    /// Turn some given flag off (in place)
    #[inline]
    pub fn unset(&mut self, f:Flag){ self.0 ^= f as u8 }

    /// Clears all flags
    #[inline]
    pub fn reset(&mut self) { self.0 = Flag::Clear as u8 }

    /// Tests the value of some given flag
    #[inline]
    pub fn is_set(&self, f: Flag) -> bool { self.0 & (f as u8) > 0 }

    #[inline]
    pub fn one_of(&self, f1: Flag, f2: Flag) -> bool {
        self.0 & (f1 as u8 | f2 as u8) > 0
    }

    #[inline]
    pub fn to_u8(&self) -> u8 { self.0 }

    #[inline]
    pub fn from(v: u8) -> Flags {
        Flags(v)
    }
}

/// Permits the use of the | operator between some `Flags` and a `Flag` to yield a new `Flag`
impl BitOr<Flag> for Flags {
    type Output = Flags;

    #[inline]
    fn bitor(self, flag: Flag) -> Flags { Flags(self.0 | flag as u8) }
}
/// Permits the use of the |= operator between some `Flags` and a `Flag` to mutate the value of the
/// flags in place.
impl BitOrAssign<Flag> for Flags {
    #[inline]
    fn bitor_assign(&mut self, flag: Flag) { self.0 |= flag as u8 }
}
/// Permits the use of the | operator between some `Flags` and a `Flag` to yield a new `Flag`
impl BitAnd<Flag> for Flags {
    type Output = Flags;

    #[inline]
    fn bitand(self, flag: Flag)-> Flags { Flags(self.0 & flag as u8) }
}
/// Permits the use of the &= operator between some `Flags` and a `Flag` to mutate the value of the
/// flags in place.
impl BitAndAssign<Flag> for Flags {
    #[inline]
    fn bitand_assign(&mut self, flag: Flag) { self.0 &= flag as u8 }
}
/// Permits the use of the | operator between some `Flags` and a `Flag` to yield a new `Flag`
impl BitXor<Flag> for Flags {
    type Output = Flags;

    #[inline]
    fn bitxor(self, flag: Flag)-> Flags { Flags(self.0 ^ flag as u8) }
}
/// Permits the use of the ^= operator between some `Flags` and a `Flag` to mutate the value of the
/// flags in place.
impl BitXorAssign<Flag> for Flags {
    #[inline]
    fn bitxor_assign(&mut self, flag: Flag) { self.0 ^= flag as u8 }
}

/// Custom implementation of the `Debug` trait. This version provides a much more helpful idea of
/// the flags that have been turned on/off in the bit set.
impl Debug for Flags {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let mut s = String::from("");

        if self.0 == (Flag::Clear as u8) {
            s = format!("{} Clear", s);
        }

        if self.is_set(Flag::IsMarked) {
            s = format!("{} IsMarked", s);
        }
        if self.is_set(Flag::IsImplied) {
            s = format!("{} IsImplied", s);
        }
        if self.is_set(Flag::IsNotImplied) {
            s = format!("{} IsNotImplied", s);
        }
        if self.is_set(Flag::IsInConflictClause) {
            s = format!("{} IsInConflictClause", s);
        }

        return write!(f, "Flags({} )", s);
    }
}