use std::ops::*;
use core::*;

// -----------------------------------------------------------------------------------------------
/// # Variable indexed vector
/// A thin wrapper around the Vec type which allows efficient and convenient indexing using some
/// Variable as index
// -----------------------------------------------------------------------------------------------
#[derive(Debug)]
pub struct VarIdxVec<T>(Vec<T>);

impl<T> VarIdxVec<T> {
    /// Creates a variable indexed vector from an existing vec
    pub fn from(v: Vec<T>) -> VarIdxVec<T> {
        VarIdxVec(v)
    }

    /// Creates a variable indexed vector capable of storing the information for `s` variables
    ///
    /// _Note:_
    /// this function only pre-allocates the heap space, you still need to `push` items in order
    /// for them to be stored
    pub fn with_capacity(s: usize) -> VarIdxVec<T> {
        VarIdxVec(Vec::with_capacity(s))
    }
}

// Allow the use of all the traits of the inner type (push, size(), swap() etc...)
impl<T> Deref for VarIdxVec<T> {
    type Target = Vec<T>;
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for VarIdxVec<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

// Allow the custom indexing
impl<T> Index<Variable> for VarIdxVec<T> {
    type Output = T;

    #[inline]
    fn index(&self, v: Variable) -> &Self::Output {
        &self.0[v.to_usize()-1]
    }
}

impl<T> IndexMut<Variable> for VarIdxVec<T> {
    #[inline]
    fn index_mut(&mut self, v: Variable) -> &mut Self::Output {
        &mut self.0[v.to_usize()-1]
    }
}
