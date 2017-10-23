//! This module contains a few utility types that let me group the code that should imho not really
//! be part of this solver, but is necessary (or at least convenient!) nonetheless.
use std::rc::*;
use std::cell::*;
use std::fmt::*;

/// Aliasable is a type for objects to whom other objects *must* be able to hold a mutable reference
///
/// # Note
/// Using an Aliasable object, it is the programmer's responsibility to make sure that aliases are
/// - not being mutated >1 times concurrently
pub struct Aliasable<T>(Rc<UnsafeCell<T>>);

impl<T> Aliasable<T> {
    /// Creates a new Aliasable object. That object is going to be heap allocated, and interior
    /// mutable.
    pub fn new(value:T) -> Aliasable<T> {
        Aliasable(Rc::new(UnsafeCell::new( value )))
    }

    /// Returns a new alias (an unchecked raw pointer) to the data held by the underlying
    /// Box<UnsafeCell>
    pub fn alias(&self) -> Alias<T> {
        Alias::new(Rc::downgrade(&self.0) )
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

#[derive(Clone)]
/// Alias is a type wrapping a raw mutable pointer. Hence, it is -- by definition -- not safe as it
/// shouldn't be mutated by two or more holders at once. It is the programmer's responsibility
/// to make sure that not such cases arise in the practice.
///
/// Roughly speaking, it has the same semantics as a Weak reference. However, it relaxes the safety
/// assumptions made by Rust in the sense that it allows you to mutate the data even though an ohter
/// Rc or Weak exists at the same time.
pub struct Alias<T> (Weak<UnsafeCell<T>>);

impl<T> Alias<T> {
    /// Creates a new alias
    fn new(ptr : Weak<UnsafeCell<T>>) -> Alias<T> {
        Alias(ptr)
    }

    /// Attempts to return the aliased information
    pub fn get(&self) -> Option<&mut T> {
        match self.0.upgrade() {
            None       => None,
            Some(cell) => Some(unsafe { &mut * cell.get() })
        }
    }
}

impl<T> Debug for Alias<T> where T : Debug {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "Alias({:?})", self.get() )
    }
}

#[cfg(test)]
mod test_aliases {
    use super::*;
    use std::mem;

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

        assert_eq!("Alias(Some([1, 2, 3, 4, 5]))", format!("{:?}", a_1));
        assert_eq!("Alias(Some([1, 2, 3, 4, 5]))", format!("{:?}", a_2));
    }

    #[test]
    fn it_must_resist_to_relocation(){
        let mut v = vec![Aliasable::new(1),
                         Aliasable::new(2),
                         Aliasable::new(3),
                         Aliasable::new(4)];

        let a = v[0].alias();

        assert_eq!("Aliasable(1)", format!("{:?}", v[0]));
        assert_eq!("Alias(Some(1))",     format!("{:?}", a));
        v.swap(0, 3);
        assert_ne!("Aliasable(1)", format!("{:?}", v[0]));
        assert_eq!("Alias(Some(1))",     format!("{:?}", a));
    }

    #[test]
    fn get_must_yield_none_when_value_is_dropped(){
        let x = vec![1, 2, 3, 4, 5];
        let a_ = Aliasable::new(x);
        let a_1 = a_.alias();

        assert_eq!("Alias(Some([1, 2, 3, 4, 5]))", format!("{:?}", a_1));
        assert_eq!("Some([1, 2, 3, 4, 5])",        format!("{:?}", a_1.get()));

        mem::drop(a_);

        assert_eq!("Alias(None)", format!("{:?}", a_1));
        assert_eq!("None",        format!("{:?}", a_1.get()));
    }
}