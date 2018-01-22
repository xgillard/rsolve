use std::string::String;
use std::marker::PhantomData;
use std::convert::{From, Into};
use std::fmt::{Debug, Formatter, Result};
use std::ops::{BitOr, BitAnd, BitOrAssign, BitAndAssign, BitXor, BitXorAssign};

/// A marker trait that indicates that a type behaves as a flag description type (typesafe
/// enumeration of values)
pub trait Flag : Into<u8> + Copy + Debug {}

/// The `LitFlag` enum is simply a type safe way to constrain the flags that can possibly be set for
/// any given literal.
#[derive(Debug, Clone, Copy)]
pub enum LitFlag {
    Clear             , //--> serves to reset all flags
    IsForced          , //--> this flag is set for all literals which are *FORCED* by the problem
    IsMarked          , //--> used during conflict analysis
    IsImplied         , //--> forced by the ongoing conflict clause
    IsNotImplied      , //--> not forced but effectively analysed
    IsInConflictClause  //--> makes it easy to retrieve the backjump point
}
/// Implement the marker type
impl Flag for LitFlag {}
/// Implement conversion to bitfield
impl From<LitFlag> for u8 {
    #[inline]
    fn from(v : LitFlag) -> u8 {
        match v {
            LitFlag::Clear              =>  0,
            LitFlag::IsForced           =>  1,
            LitFlag::IsMarked           =>  2,
            LitFlag::IsImplied          =>  4,
            LitFlag::IsNotImplied       =>  8,
            LitFlag::IsInConflictClause => 16
        }
    }
}

/// The `ClauseFlag` enum is simply a type safe way to specify some meta information about any given
/// clause. These are notably used during preprocessing.
#[derive(Debug, Clone, Copy)]
pub enum ClauseFlag {
    Clear         , //--> serves to reset all flags
    IsAdded       , //--> the clause was added to the database
    IsDeleted     , //--> the clause is stale. It was marked for deletion but hasn't been removed yet
    IsStrengthened  //--> the clause has been strenghtened by self subsuming resolution
}
/// Implement the marker type
impl Flag for ClauseFlag {}
/// Implement the conversion to bit field
impl From<ClauseFlag> for u8 {
    #[inline]
    fn from(v : ClauseFlag) -> u8 {
        match v {
            ClauseFlag::Clear               =>  0,
            ClauseFlag::IsAdded             =>  1,
            ClauseFlag::IsDeleted           =>  2,
            ClauseFlag::IsStrengthened      =>  4
        }
    }
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
pub struct Flags<FlagType : Flag> {
    data  : u8,
    _spook: PhantomData<FlagType> // 0-sized info to let compiler know when we're messing up different types of flags
}

impl<FlagType : Flag>  Flags<FlagType> {
    /// Constructor
    #[inline]
    pub fn new() -> Flags<FlagType> {
        Flags::from(0)
     }

    /// Turn on some given flag _in place_
    #[inline]
    pub fn set(&mut self, f: FlagType) { self.data |= f.into() }

    /// Turn some given flag off (in place)
    #[inline]
    pub fn unset(&mut self, f: FlagType){ self.data ^= f.into() }

    /// Clears all flags
    #[inline]
    pub fn reset(&mut self) { self.data = 0 }

    /// Tests the value of some given flag
    #[inline]
    pub fn is_set(&self, f: FlagType) -> bool { self.data & (f.into()) > 0 }

    #[inline]
    pub fn one_of(&self, f1: FlagType, f2: FlagType) -> bool {
        self.data & (f1.into() | f2.into()) > 0
    }
}

/// Conversion from u8 to typed flags set
impl<T : Flag> From<u8> for Flags<T> {
    #[inline]
    fn from(v: u8) -> Flags<T> {
        Flags::<T> { data : v, _spook: PhantomData }
    }
}

impl<T : Flag> From<Flags<T>> for u8 {
    #[inline]
    fn from(v : Flags<T>) -> u8 { v.data }
}

/// Permits the use of the | operator between some `Flags` and a `Flag` to yield a new `Flag`
impl<T : Flag> BitOr<T> for Flags<T> {
    type Output = Flags<T>;

    #[inline]
    fn bitor(self, flag: T) -> Flags<T> { Flags::from(self.data | flag.into()) }
}
/// Permits the use of the |= operator between some `Flags` and a `Flag` to mutate the value of the
/// flags in place.
impl<T : Flag> BitOrAssign<T> for Flags<T> {
    #[inline]
    fn bitor_assign(&mut self, flag: T) { self.data |= flag.into() }
}
/// Permits the use of the | operator between some `Flags` and a `Flag` to yield a new `Flag`
impl<T : Flag> BitAnd<T> for Flags<T> {
    type Output = Flags<T>;

    #[inline]
    fn bitand(self, flag: T) -> Flags<T> { Flags::from(self.data & flag.into()) }
}
/// Permits the use of the &= operator between some `Flags` and a `Flag` to mutate the value of the
/// flags in place.
impl<T : Flag> BitAndAssign<T> for Flags<T> {
    #[inline]
    fn bitand_assign(&mut self, flag: T) { self.data &= flag.into() }
}
/// Permits the use of the | operator between some `Flags` and a `Flag` to yield a new `Flag`
impl<T : Flag> BitXor<T> for Flags<T> {
    type Output = Flags<T>;

    #[inline]
    fn bitxor(self, flag: T) -> Flags<T> { Flags::from(self.data ^ flag.into()) }
}
/// Permits the use of the ^= operator between some `Flags` and a `Flag` to mutate the value of the
/// flags in place.
impl<T : Flag> BitXorAssign<T> for Flags<T> {
    #[inline]
    fn bitxor_assign(&mut self, flag: T) { self.data ^= flag.into() }
}

/// Custom implementation of the `Debug` trait for literal flags. This version provides a much more
/// helpful idea of the flags that have been turned on/off in the bit set.
impl Debug for Flags<LitFlag> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let mut s = String::from("");

        if self.data == u8::from(LitFlag::Clear) {
            s = format!("{} Clear", s);
        }

        if self.is_set(LitFlag::IsMarked) {
            s = format!("{} IsMarked", s);
        }
        if self.is_set(LitFlag::IsImplied) {
            s = format!("{} IsImplied", s);
        }
        if self.is_set(LitFlag::IsNotImplied) {
            s = format!("{} IsNotImplied", s);
        }
        if self.is_set(LitFlag::IsInConflictClause) {
            s = format!("{} IsInConflictClause", s);
        }

        return write!(f, "Flags({} )", s);
    }
}

/// Custom implementation of the `Debug` trait for literal flags. This version provides a much more
/// helpful idea of the flags that have been turned on/off in the bit set.
impl Debug for Flags<ClauseFlag> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        let mut s = String::from("");

        if self.data == u8::from(LitFlag::Clear) {
            s = format!("{} Clear", s);
        }

        if self.is_set(ClauseFlag::IsAdded) {
            s = format!("{} IsAdded", s);
        }
        if self.is_set(ClauseFlag::IsDeleted) {
            s = format!("{} IsDeleted", s);
        }
        if self.is_set(ClauseFlag::IsStrengthened) {
            s = format!("{} IsStrengthened", s);
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

        assert!(! x.is_set(LitFlag::IsImplied) );
        assert!(! x.is_set(LitFlag::IsNotImplied) );
        assert!(! x.is_set(LitFlag::IsMarked) );
        assert!(! x.is_set(LitFlag::IsInConflictClause) );

        x.set(LitFlag::IsImplied);
        x.set(LitFlag::IsMarked);

        assert!(  x.is_set(LitFlag::IsImplied) );
        assert!(! x.is_set(LitFlag::IsNotImplied) );
        assert!(  x.is_set(LitFlag::IsMarked) );
        assert!(! x.is_set(LitFlag::IsInConflictClause) );
    }

    // unset should turn some flag off
    #[test]
    fn unset_should_turn_some_flag_off(){
        let mut x = Flags::new();

        assert!(! x.is_set(LitFlag::IsImplied) );
        assert!(! x.is_set(LitFlag::IsNotImplied) );
        assert!(! x.is_set(LitFlag::IsMarked) );
        assert!(! x.is_set(LitFlag::IsInConflictClause) );

        x.set(LitFlag::IsImplied);
        x.set(LitFlag::IsMarked);

        assert!(  x.is_set(LitFlag::IsImplied) );
        assert!(! x.is_set(LitFlag::IsNotImplied) );
        assert!(  x.is_set(LitFlag::IsMarked) );
        assert!(! x.is_set(LitFlag::IsInConflictClause) );

        x.unset(LitFlag::IsMarked);

        assert!(  x.is_set(LitFlag::IsImplied) );
        assert!(! x.is_set(LitFlag::IsNotImplied) );
        assert!(! x.is_set(LitFlag::IsMarked) );
        assert!(! x.is_set(LitFlag::IsInConflictClause) );

    }
    // reset should wipe everything off
    #[test]
    fn reset_should_wipe_everything_off(){
        let mut x = Flags::new();

        assert!(! x.is_set(LitFlag::IsImplied) );
        assert!(! x.is_set(LitFlag::IsNotImplied) );
        assert!(! x.is_set(LitFlag::IsMarked) );
        assert!(! x.is_set(LitFlag::IsInConflictClause) );

        x.set(LitFlag::IsImplied);
        x.set(LitFlag::IsMarked);

        assert!(  x.is_set(LitFlag::IsImplied) );
        assert!(! x.is_set(LitFlag::IsNotImplied) );
        assert!(  x.is_set(LitFlag::IsMarked) );
        assert!(! x.is_set(LitFlag::IsInConflictClause) );

        x.reset();
        assert!(! x.is_set(LitFlag::IsImplied) );
        assert!(! x.is_set(LitFlag::IsNotImplied) );
        assert!(! x.is_set(LitFlag::IsMarked) );
        assert!(! x.is_set(LitFlag::IsInConflictClause) );
    }
    // is_set should tell whether x is set
    #[test]
    fn is_set_should_tell_whether_some_flag_is_on(){
        let mut x = Flags::new();

        assert!(! x.is_set(LitFlag::IsImplied) );
        assert!(! x.is_set(LitFlag::IsNotImplied) );
        assert!(! x.is_set(LitFlag::IsMarked) );
        assert!(! x.is_set(LitFlag::IsInConflictClause) );

        x.set(LitFlag::IsImplied);
        x.set(LitFlag::IsMarked);

        assert!(  x.is_set(LitFlag::IsImplied) );
        assert!(! x.is_set(LitFlag::IsNotImplied) );
        assert!(  x.is_set(LitFlag::IsMarked) );
        assert!(! x.is_set(LitFlag::IsInConflictClause) );
    }

    // is_set should tell whether x is set
    #[test]
    fn one_of_should_tell_whether_some_flag_is_on(){
        let mut x = Flags::new();

        assert!(! x.is_set(LitFlag::IsImplied) );
        assert!(! x.is_set(LitFlag::IsNotImplied) );
        assert!(! x.is_set(LitFlag::IsMarked) );
        assert!(! x.is_set(LitFlag::IsInConflictClause) );

        x.set(LitFlag::IsImplied);
        x.set(LitFlag::IsMarked);

        assert!( x.one_of(LitFlag::IsImplied, LitFlag::IsNotImplied) );
        assert!( x.one_of(LitFlag::IsImplied, LitFlag::IsMarked) );
        assert!( x.one_of(LitFlag::IsImplied, LitFlag::IsInConflictClause) );

        assert!( x.one_of(LitFlag::IsMarked, LitFlag::IsImplied) );
        assert!( x.one_of(LitFlag::IsMarked, LitFlag::IsNotImplied) );
        assert!( x.one_of(LitFlag::IsMarked, LitFlag::IsInConflictClause) );

        assert!( x.one_of(LitFlag::IsNotImplied, LitFlag::IsImplied) );
        assert!( x.one_of(LitFlag::IsNotImplied, LitFlag::IsMarked) );
        assert!(!x.one_of(LitFlag::IsNotImplied, LitFlag::IsInConflictClause) );

        assert!( x.one_of(LitFlag::IsInConflictClause, LitFlag::IsImplied) );
        assert!( x.one_of(LitFlag::IsInConflictClause, LitFlag::IsMarked) );
        assert!(!x.one_of(LitFlag::IsInConflictClause, LitFlag::IsNotImplied) );
    }

    // |   should yield
    #[test]
    fn pipe_op_should_yield(){
        let x = Flags::<LitFlag>::from(0);
        assert_eq!(u8::from(x | LitFlag::IsMarked), LitFlag::IsMarked.into());
    }
    // |=  shoudl mutate
    #[test]
    fn pipe_eq_op_should_mutate(){
        let mut x = Flags::<LitFlag>::from(0);
        x |= LitFlag::IsMarked;

        assert_eq!( u8::from(x) , LitFlag::IsMarked.into());
    }
    // &   should yield
    #[test]
    fn and_op_should_yield(){
        let x = Flags::<LitFlag>::from(u8::from(LitFlag::IsMarked));
        assert_eq!(u8::from(x & LitFlag::IsMarked), LitFlag::IsMarked.into());

        let x = Flags::<LitFlag>::from(u8::from(LitFlag::IsImplied));
        assert_eq!(u8::from(LitFlag::IsImplied), x.data);
        assert_eq!(0_u8, u8::from(x & LitFlag::IsMarked));
    }
    // &=  should yield
    #[test]
    fn and_eq_op_should_mutate(){
        let mut x = Flags::<LitFlag>::from(u8::from(LitFlag::IsMarked));

        x &= LitFlag::IsMarked;
        assert_eq!(u8::from(x), LitFlag::IsMarked.into() );

        x &= LitFlag::IsImplied;
        assert_eq!( u8::from(x), 0_u8 );
    }
    // ^   should yield
    #[test]
    fn xor_op_should_yield(){
        let x = Flags::new();
        assert_eq!(u8::from(x ^ LitFlag::IsMarked), LitFlag::IsMarked.into());

        let x = Flags::<LitFlag>::from(u8::from(LitFlag::IsImplied));
        assert_eq!(u8::from(x ^ LitFlag::IsImplied), 0_u8 );
    }
    // ^=  should mutate
    #[test]
    fn xor_eq_op_should_mutate(){
        let mut x = Flags::new();

        x ^= LitFlag::IsMarked;
        assert_eq!(u8::from(x), LitFlag::IsMarked.into() );

        x ^= LitFlag::IsMarked;
        assert_eq!(u8::from(x) , 0_u8 );
    }

    // debug ?
}