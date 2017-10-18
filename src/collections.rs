use std::ops::*;
use super::*;

// -----------------------------------------------------------------------------------------------
// Variable indexed vector
// -----------------------------------------------------------------------------------------------
#[derive(Debug)]
pub struct VarIdxVec<T>(Vec<T>);

impl<T> VarIdxVec<T> {
    pub fn from(v: Vec<T>) -> VarIdxVec<T> {
        VarIdxVec(v)
    }

    pub fn with_capacity(s: usize) -> VarIdxVec<T> {
        VarIdxVec(Vec::with_capacity(s))
    }
}

// Allow the use of all the traits of the inner type
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
// Literal indexed vector
// -----------------------------------------------------------------------------------------------
#[derive(Debug)]
pub struct LitIdxVec<T>(Vec<T>);

impl<T> LitIdxVec<T> {
    pub fn with_capacity(s: usize) -> LitIdxVec<T> {
        LitIdxVec(Vec::with_capacity(2*s))
    }
    pub fn push_values(&mut self, positive_value: T, negative_value: T) {
        self.0.push(positive_value);
        self.0.push(negative_value);
    }
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
mod test_lit_idx_vec {
    use super::*;

    #[test]
    fn push_init_interleaves_positive_and_negative(){
        let mut v = LitIdxVec::with_capacity(6);

        for i in 1..7 {
            let mut phase = -1;
            v.push_init(&mut || {
                let ret = i * phase;
                phase *= -1;
                return ret
            });
        }

        assert_eq!("LitIdxVec([-1, 1, -2, 2, -3, 3, -4, 4, -5, 5, -6, 6])", format!("{:?}", v))
    }

    #[test]
    fn index() {
        let mut v = LitIdxVec::with_capacity(100);

        for i in 1..101 {
            let mut phase = -1;
            v.push_init(&mut || {
                let ret = i * phase;
                phase *= -1;
                return ret
            });
        }

        for i in 1..7 {
            assert_eq!( i, v[Literal::from( i)] );
            assert_eq!(-i, v[Literal::from(-i)] );
        }
    }
}