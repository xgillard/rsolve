use std::string::String;
use std::fmt::{Debug, Formatter, Result};
use std::ops::{BitOr, BitAnd, BitOrAssign, BitAndAssign, BitXor, BitXorAssign};

/// The `Flag` enum is simply a type safe way to constrain the flags that can possibly be set for
/// any given literal.
#[derive(Debug)]
pub enum Flag {
    Clear              =  0, //--> serves to reset all flags
    IsFalse            =  1, //--> when the literal is assigned false
    IsMarked           =  2, //--> used during conflict analysis
    IsImplied          =  4, //--> forced by the onoing c. clause
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

        if self.is_set(Flag::IsFalse) {
            s = format!("{} IsFalse", s);
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

#[cfg(test)]
mod tests {
    use super::*;

    // set should turn some flag on
    #[test]
    fn set_should_turn_some_flag_on(){
        let mut x = Flags::new();

        assert!(! x.is_set(Flag::IsFalse) );
        assert!(! x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(! x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );

        x.set(Flag::IsFalse);
        x.set(Flag::IsMarked);

        assert!(  x.is_set(Flag::IsFalse) );
        assert!(! x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(  x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );
    }

    // unset should turn some flag off
    #[test]
    fn unset_should_turn_some_flag_off(){
        let mut x = Flags::new();

        assert!(! x.is_set(Flag::IsFalse) );
        assert!(! x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(! x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );

        x.set(Flag::IsFalse);
        x.set(Flag::IsMarked);

        assert!(  x.is_set(Flag::IsFalse) );
        assert!(! x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(  x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );

        x.unset(Flag::IsMarked);
        assert!(  x.is_set(Flag::IsFalse) );
        assert!(! x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(! x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );

    }
    // reset should wipe everything off
    #[test]
    fn reset_should_wipe_everything_off(){
        let mut x = Flags::new();

        assert!(! x.is_set(Flag::IsFalse) );
        assert!(! x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(! x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );

        x.set(Flag::IsFalse);
        x.set(Flag::IsMarked);

        assert!(  x.is_set(Flag::IsFalse) );
        assert!(! x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(  x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );

        x.reset();
        assert!(! x.is_set(Flag::IsFalse) );
        assert!(! x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(! x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );
    }
    // is_set should tell whether x is set
    #[test]
    fn is_set_should_tell_whether_some_flag_is_on(){
        let mut x = Flags::new();

        assert!(! x.is_set(Flag::IsFalse) );
        assert!(! x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(! x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );

        x.set(Flag::IsFalse);
        x.set(Flag::IsMarked);

        assert!(  x.is_set(Flag::IsFalse) );
        assert!(! x.is_set(Flag::IsImplied) );
        assert!(! x.is_set(Flag::IsNotImplied) );
        assert!(  x.is_set(Flag::IsMarked) );
        assert!(! x.is_set(Flag::IsInConflictClause) );
    }

    // |   should yield
    #[test]
    fn pipe_op_should_yield(){
        let x = Flags(0);

        assert_eq!( (x | Flag::IsMarked).0 , (Flags(Flag::IsMarked as u8)).0 );
    }
    // |=  shoudl mutate
    #[test]
    fn pipe_eq_op_should_mutate(){
        let mut x = Flags(0);
        x |= Flag::IsMarked;

        assert_eq!( x.0 , (Flags(Flag::IsMarked as u8)).0 );
    }
    // &   should yield
    #[test]
    fn and_op_should_yield(){
        let x = Flags(Flag::IsMarked as u8);
        assert_eq!( (x & Flag::IsMarked).0 , (Flags(Flag::IsMarked as u8)).0 );

        let x = Flags(Flag::IsFalse as u8);
        assert_eq!( (x & Flag::IsMarked).0 , 0_u8 );
    }
    // &=  should yield
    #[test]
    fn and_eq_op_should_mutate(){
        let mut x = Flags(Flag::IsMarked as u8);

        x &= Flag::IsMarked;
        assert_eq!( x.0 , Flag::IsMarked as u8 );

        x &= Flag::IsFalse;
        assert_eq!( x.0 , 0_u8 );
    }
    // ^   should yield
    #[test]
    fn xor_op_should_yield(){
        let x = Flags::new();
        assert_eq!( (x ^ Flag::IsMarked).0 , (Flags(Flag::IsMarked as u8)).0 );

        let x = Flags(Flag::IsFalse as u8);
        assert_eq!( (x ^ Flag::IsFalse).0 , 0_u8 );
    }
    // ^=  should mutate
    #[test]
    fn xor_eq_op_should_mutate(){
        let mut x = Flags::new();

        x ^= Flag::IsMarked;
        assert_eq!( x.0 , Flag::IsMarked as u8 );

        x ^= Flag::IsMarked;
        assert_eq!( x.0 , 0_u8 );
    }

    // debug ?
}