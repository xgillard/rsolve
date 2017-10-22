//! This module contains a few utility types that let me group the code that should imho not really
//! be part of this solver, but is necessary (or at least convenient!) nonetheless.

use std::boxed::Box;
use std::cell::UnsafeCell;

use std::ops::{Deref, DerefMut};
use std::fmt::*;

/// Aliasable is a type for objects to whom other objects *must* be able to hold a mutable reference
///
/// # Note
/// Using an Aliasable object, it is the programmer's responsibility to make sure that aliases are
/// - not being mutated >1 times concurrently
/// - not dangling
pub struct Aliasable<T>(Box<UnsafeCell<T>>);

impl<T> Aliasable<T> {
    /// Creates a new Aliasable object. That object is going to be heap allocated, and interior
    /// mutable.
    pub fn new(value:T) -> Aliasable<T> {
        Aliasable(Box::new(UnsafeCell::new(value)))
    }

    /// Returns a new alias (an unchecked raw pointer) to the data held by the underlying
    /// Box<UnsafeCell>
    pub fn alias(&self) -> Alias<T> {
        Alias(self.0.get())
    }
}

impl<T> From<T> for Aliasable<T> {
    fn from(value: T) -> Aliasable<T> {
        Aliasable::new(value)
    }
}

impl<T> Debug for Aliasable<T> where T : Debug {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "Aliasable({:?})", unsafe { &*self.0.get() })
    }
}

#[derive(Clone, Eq)]
/// Alias is a type wrapping a raw mutable pointer. Hence, it is -- by definition -- not safe as it
/// might dangle or be mutated by two or more holders at once. It is the programmer's responsibility
/// to make sure that not such cases arise in the practice.
///
/// # Note:
/// For the convenience (and even though this is definitely not safe !) we allow an alias to behave
/// like a regular smart pointer.
pub struct Alias<T> (*mut T);

impl<T> Deref for Alias<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T { unsafe {& *self.0} }
}

impl <T> DerefMut for Alias<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {unsafe {&mut *self.0} }
}

impl<T> Debug for Alias<T> where T : Debug {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "Alias({:?})", unsafe { &*self.0 })
    }
}

impl<T> PartialEq for Alias<T> {
    fn eq(&self, other: &Alias<T>) -> bool {
        self.0 == other.0
    }
}

#[cfg(test)]
mod test_aliases {
    use super::*;

    #[test]
    fn test_creation() {
        let x = vec![1, 2, 3, 4, 5];
        let a_ = Aliasable::new(x);

        assert_eq!("Aliasable([1, 2, 3, 4, 5])", format!("{:?}", a_));
    }

    #[test]
    fn test_alias(){
        let x = vec![1, 2, 3, 4, 5];
        let a_ = Aliasable::new(x);
        let a_1 = a_.alias();
        let a_2 = a_.alias();

        assert_eq!("Alias([1, 2, 3, 4, 5])", format!("{:?}", a_1));
        assert_eq!("Alias([1, 2, 3, 4, 5])", format!("{:?}", a_2));
    }

    #[test]
    fn test_eq(){
        let x = vec![1, 2, 3, 4, 5];
        let a_ = Aliasable::new(x);
        let a_1 = a_.alias();
        let a_2 = a_.alias();

        assert_eq!(a_1, a_2);
    }

    #[test]
    fn it_must_resist_to_relocation(){
        let mut v = vec![Aliasable::new(1),
                         Aliasable::new(2),
                         Aliasable::new(3),
                         Aliasable::new(4)];

        let a = v[0].alias();

        assert_eq!("Aliasable(1)", format!("{:?}", v[0]));
        assert_eq!("Alias(1)",     format!("{:?}", a));
        v.swap(0, 3);
        assert_ne!("Aliasable(1)", format!("{:?}", v[0]));
        assert_eq!("Alias(1)",     format!("{:?}", a));
    }
}