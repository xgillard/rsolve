use std::string::String;
use std::fmt::{Debug, Formatter, Result};
use std::ops::{BitOr, BitAnd, BitOrAssign, BitAndAssign, BitXor, BitXorAssign};

/// The `Flag` enum is simply a type safe way to constrain the flags that can possibly be set for
/// any given literal.
#[derive(Debug)]
pub enum Flag {
    Clear              =  0, //--> serves to reset all flags
    IsForced           =  1, //--> this flag is set for all literals which are *FORCED* by the problem
    IsMarked           =  2, //--> used during conflict analysis
    IsImplied          =  4, //--> forced by the ongoing conflict clause
    IsNotImplied       =  8, //--> not forced but effectively analysed
    IsInConflictClause = 16  //--> makes it easy to retrieve the backjump point
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

    #[inline]
    pub fn from(v: u8) -> Flags {
        Flags(v)
    }

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

// -----------------------------------------------------------------------------------------------
/// # Unit Tests
// -----------------------------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;

    // set should turn some flag on
    #[test]
    fn set_should_turn_some_flag_on(){
        let mut x = Flags::new();

        assert!(! x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(! x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );

        x.set(Flag::IsImplied);
        x.set(Flag::IsMarked);

        assert!(  x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(  x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );
    }

    // unset should turn some flag off
    #[test]
    fn unset_should_turn_some_flag_off(){
        let mut x = Flags::new();

        assert!(! x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(! x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );

        x.set(Flag::IsImplied);
        x.set(Flag::IsMarked);

        assert!(  x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(  x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );

        x.unset(Flag::IsMarked);

        assert!(  x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(! x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );

    }
    // reset should wipe everything off
    #[test]
    fn reset_should_wipe_everything_off(){
        let mut x = Flags::new();

        assert!(! x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(! x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );

        x.set(Flag::IsImplied);
        x.set(Flag::IsMarked);

        assert!(  x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(  x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );

        x.reset();
        assert!(! x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(! x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );
    }
    // is_set should tell whether x is set
    #[test]
    fn is_set_should_tell_whether_some_flag_is_on(){
        let mut x = Flags::new();

        assert!(! x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(! x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );

        x.set(Flag::IsImplied);
        x.set(Flag::IsMarked);

        assert!(  x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(  x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );
    }

    // is_set should tell whether x is set
    #[test]
    fn one_of_should_tell_whether_some_flag_is_on(){
        let mut x = Flags::new();

        assert!(! x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(! x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );

        x.set(Flag::IsImplied);
        x.set(Flag::IsMarked);

        assert!( x.one_of(Flag::IsImplied, Flag::IsNotImplied) );
        assert!( x.one_of(Flag::IsImplied, Flag::IsMarked) );
        assert!( x.one_of(Flag::IsImplied, Flag::IsInConflictClause) );

        assert!( x.one_of(Flag::IsMarked, Flag::IsImplied) );
        assert!( x.one_of(Flag::IsMarked, Flag::IsNotImplied) );
        assert!( x.one_of(Flag::IsMarked, Flag::IsInConflictClause) );

        assert!( x.one_of(Flag::IsNotImplied, Flag::IsImplied) );
        assert!( x.one_of(Flag::IsNotImplied, Flag::IsMarked) );
        assert!(!x.one_of(Flag::IsNotImplied, Flag::IsInConflictClause) );

        assert!( x.one_of(Flag::IsInConflictClause, Flag::IsImplied) );
        assert!( x.one_of(Flag::IsInConflictClause, Flag::IsMarked) );
        assert!(!x.one_of(Flag::IsInConflictClause, Flag::IsNotImplied) );
    }

    // |   should yield
    #[test]
    fn pipe_op_should_yield(){
        let x = Flags::from(0);

        assert_eq!( (x | Flag::IsMarked).to_u8() , (Flags::from(Flag::IsMarked as u8)).to_u8() );
    }
    // |=  shoudl mutate
    #[test]
    fn pipe_eq_op_should_mutate(){
        let mut x = Flags::from(0);
        x |= Flag::IsMarked;

        assert_eq!( x.to_u8() , (Flags::from(Flag::IsMarked as u8)).to_u8() );
    }
    // &   should yield
    #[test]
    fn and_op_should_yield(){
        let x = Flags::from(Flag::IsMarked as u8);
        assert_eq!( (x & Flag::IsMarked).to_u8() , (Flags::from(Flag::IsMarked as u8)).to_u8() );

        let x = Flags::from(Flag::IsImplied as u8);
        assert_eq!( (x & Flag::IsMarked).to_u8() , 0_u8 );
    }
    // &=  should yield
    #[test]
    fn and_eq_op_should_mutate(){
        let mut x = Flags::from(Flag::IsMarked as u8);

        x &= Flag::IsMarked;
        assert_eq!( x.to_u8() , Flag::IsMarked as u8 );

        x &= Flag::IsImplied;
        assert_eq!( x.to_u8() , 0_u8 );
    }
    // ^   should yield
    #[test]
    fn xor_op_should_yield(){
        let x = Flags::new();
        assert_eq!( (x ^ Flag::IsMarked).to_u8() , (Flags::from(Flag::IsMarked as u8)).to_u8() );

        let x = Flags::from(Flag::IsImplied as u8);
        assert_eq!( (x ^ Flag::IsImplied).to_u8() , 0_u8 );
    }
    // ^=  should mutate
    #[test]
    fn xor_eq_op_should_mutate(){
        let mut x = Flags::new();

        x ^= Flag::IsMarked;
        assert_eq!( x.to_u8() , Flag::IsMarked as u8 );

        x ^= Flag::IsMarked;
        assert_eq!( x.to_u8() , 0_u8 );
    }

    // debug ?
}