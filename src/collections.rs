use std::ops::*;
use super::*;

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

// -----------------------------------------------------------------------------------------------
/// # Literal indexed vector
/// A thin wrapper around the Vec type which allows efficient and convenient indexing using some
/// Literal as index.
///
/// _Note:_
/// This type tries to be smart and allocates 2 vec cells for each variable. It forces you to
/// initialize both values whenever you want to grow the 'logical size' of the array.
// -----------------------------------------------------------------------------------------------
#[derive(Debug)]
pub struct LitIdxVec<T>(Vec<T>);

impl<T> LitIdxVec<T> {
    /// Creates a literal indexed vector capable of holding 2s literals
    pub fn with_capacity(s: usize) -> LitIdxVec<T> {
        LitIdxVec(Vec::with_capacity(2*s))
    }
    /// Push the initial values associated with a new positive and negative literal
    pub fn push_values(&mut self, positive_value: T, negative_value: T) {
        self.0.push(negative_value);
        self.0.push(positive_value);
    }
    /// Push the initial values associated with a new positive and negative literal but uses an
    /// initializer function (closure) to generate the initial values
    pub fn push_init(&mut self, initializer: &mut FnMut()->T) {
        self.push_values(initializer(), initializer())
    }
}

// Allow the use of all the traits of the inner type (dubious, this can be somewhat dangerous)
impl<T> Deref for LitIdxVec<T> {
    type Target = Vec<T>;
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<T> DerefMut for LitIdxVec<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

// Allow the custom indexing
impl<T> Index<Literal> for LitIdxVec<T> {
    type Output = T;
    #[inline]
    fn index(&self, l: Literal) -> &Self::Output {
        let x = l.to_isize().abs() as usize;

        match l.sign() {
            Sign::Negative => &self.0[ (x-1) * 2   ],
            Sign::Positive => &self.0[ (x-1) * 2 +1],
        }
    }
}
impl<T> IndexMut<Literal> for LitIdxVec<T> {
    #[inline]
    fn index_mut(&mut self, l: Literal) -> &mut Self::Output {
        let x = l.to_isize().abs() as usize;

        match l.sign() {
            Sign::Negative => &mut self.0[ (x-1) * 2   ],
            Sign::Positive => &mut self.0[ (x-1) * 2 +1],
        }
    }
}


#[cfg(test)]
mod test_var_idx_vec {
    use super::*;

    #[test]
    fn with_capacity_preallocates_memory(){
        let v = VarIdxVec::<u8>::with_capacity(5);

        // granted, this feels weird !
        assert_eq!(v.capacity(), 5);
    }

    #[test]
    fn index_retrieves_the_right_info() {
        let mut v = VarIdxVec::<u8>::with_capacity(5);

        for i in 1..6 {
            v.push(i);
        }

        for i in 1..6 {
            assert_eq!( i, v[Variable::from( i as uint)] );
        }
    }

    #[test]
    #[should_panic]
    fn index_checks_upper_bound() {
        let mut v = VarIdxVec::<u8>::with_capacity(5);

        for i in 1..6 {
            v.push(i);
        }

        for i in 1..6 {
            assert_eq!( i, v[Variable::from( i as uint)] );
        }

        v[Variable::from(42)];
    }

    #[test]
    fn index_mut_updates_the_right_value(){
        let mut v = VarIdxVec::<u8>::with_capacity(5);

        for i in 1..6 {
            v.push(i);
        }

        v[Variable::from(2)] = 64;
        assert_eq!("VarIdxVec([1, 64, 3, 4, 5])", format!("{:?}", v))
    }
}

#[cfg(test)]
mod test_lit_idx_vec {
    use super::*;

    #[test]
    fn with_capacity_preallocates_memory(){
        let v = LitIdxVec::<u8>::with_capacity(5);

        // granted, this feels weird !
        assert_eq!(v.capacity(), 10);
    }

    #[test]
    fn push_values_interleaves_positive_and_negative(){
        let mut v = LitIdxVec::with_capacity(6);

        for i in 1..7 {
            v.push_values(i, -i);
        }

        assert_eq!("LitIdxVec([-1, 1, -2, 2, -3, 3, -4, 4, -5, 5, -6, 6])", format!("{:?}", v))
    }

    #[test]
    fn push_init_interleaves_positive_and_negative(){
        let mut v = LitIdxVec::with_capacity(6);

        for i in 1..7 {
            let mut phase = 1;
            v.push_init(&mut || {
                let ret = i * phase;
                phase *= -1;
                return ret
            });
        }

        assert_eq!("LitIdxVec([-1, 1, -2, 2, -3, 3, -4, 4, -5, 5, -6, 6])", format!("{:?}", v))
    }

    #[test]
    fn index_retrieves_the_right_info() {
        let mut v = LitIdxVec::with_capacity(100);

        for i in 1..101 {
            v.push_values(i, -i);
        }

        for i in 1..101 {
            assert_eq!( i, v[Literal::from( i)] );
            assert_eq!(-i, v[Literal::from(-i)] );
        }
    }

    #[test]
    #[should_panic]
    fn index_checks_lower_bound() {
        let mut v = LitIdxVec::with_capacity(6);

        for i in 1..7 {
            v.push_values(i, -i);
        }

        v[Literal::from(-12)];
    }
    #[test]
    #[should_panic]
    fn index_checks_upper_bound() {
        let mut v = LitIdxVec::with_capacity(6);

        for i in 1..7 {
            v.push_values(i, -i);
        }

        v[Literal::from(12)];
    }

    #[test]
    fn index_mut_updates_the_right_value(){
        let mut v = LitIdxVec::with_capacity(6);

        for i in 1..7 {
            v.push_values(i, -i);
        }

        v[Literal::from( 2)] = 42;
        v[Literal::from(-2)] = 64;

        assert_eq!("LitIdxVec([-1, 1, 64, 42, -3, 3, -4, 4, -5, 5, -6, 6])", format!("{:?}", v))
    }
}

