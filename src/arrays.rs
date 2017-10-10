extern crate libc;

use std::fmt;
use std::mem;
use std::ops::{Drop, Index, IndexMut};

/************* TYPES ******************************************************************************/
/* ----------- PLAIN ARRAY -----------------------------------------------------------------------*/
/// A plain array of T's allocated at runtime
///
/// # Note:
/// All operations (except for the creation) are in $\Theta(1)$
///
/// # Caveat
/// * This data structure makes no effort to free the information associated with the elements
///   referenced by the buffer cells.
/// * If ever NULL is referenced, the code will trigger panic!
///
pub struct Array<T> {
    /// the size of the content
    len: usize,
    /// the buffer holding the data
    buf: *mut T
}

impl <T> Array<T> {
    /// Constructs a new array with some given size, which one is fixed once and for all.
    /// This kind of array is never reszied
    pub fn new(sz: usize) -> Array<T> {
        unsafe {
            return Array {
                len : sz,
                buf : libc::malloc(sz * mem::size_of::<T>() ) as *mut T
            }
        }
    }

    /// Checks that `idx` respects the bounds of the array. Otherwise, it panics with an
    /// helpful message
    #[inline]
    fn check_bounds(&self, idx: usize) {
        if idx >= self.len {
            panic!("{} is not a valid index: the allowed range is 0..{}", idx, self.len-1);
        }
    }
}
impl <T> Drop for Array<T> {
    /// Whenever an Array<T> is dropped, it frees the heap allocated buffer. However, nothing is
    /// done to free the objects that might be referenced by the buffer cells.
    fn drop(&mut self) {
        unsafe {
            libc::free(self.buf as *mut libc::c_void);
        }
    }
}

impl <T> Index<usize> for Array<T> {
    type Output = T;

    /// An array can be indexed with integer. The given index is to be understood as a simple offset
    /// from the start of the buffer. This function returns an *immutable* reference to an element
    /// of the array.
    #[inline]
    fn index(&self, idx:usize) -> &T {
        self.check_bounds(idx);
        unsafe {
            let idx = idx as isize;
            return self.buf.offset(idx).as_ref().unwrap();
        }
    }
}

impl <T> IndexMut<usize> for Array<T> {
    /// An array can be indexed with integer. The given index is to be understood as a simple offset
    /// from the start of the buffer. This function returns an *immutable* reference to an element
    /// of the array.
    #[inline]
    fn index_mut(&mut self, idx:usize) -> &mut T {
        self.check_bounds(idx);
        unsafe {
            let idx = idx as isize;
            return self.buf.offset(idx).as_mut().unwrap();
        }
    }
}

impl <T : fmt::Debug > fmt::Debug for Array<T> {
    /// Provides a debug formatter for the Arrays. This eases the debugging by showing the whole
    /// content of the array.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut res = String::from("Array [ ");

        for i in 0..self.len {
            if i == 0 {
                res.push_str(format!("{:?}", self[i]).as_str());
            } else {
                res.push_str(format!(", {:?}", self[i]).as_str());
            }
        }

        res.push_str(" ]");
        return write!(f, "{}", res);
    }
}

/* ----------- LITERALS MAP ----------------------------------------------------------------------*/
/// This type is meant to easily and efficiently retrieve data associated with a some literal.
/// Therefore is is implemented as a contiguous zone of memory for which the reference points to
/// the _central_ cell of the buffer. Therefore, a `LiteralsMap` can safely be indexed by the
/// literal itself.
///
/// # Note:
/// All operations (except for the creation) are in $\Theta(1)$
///
/// # Caveat
/// * This data structure makes no effort to free the information associated with the elements
///   referenced by the buffer cells.
/// * If ever NULL is referenced, the code will trigger panic!
///
pub struct LiteralsMap<T> {
    /// The number of variables that can be held in this `map`
    nb_var: isize,
    /// The pointer towards the data buffer
    buf   : *mut T
}

impl <T> LiteralsMap<T> {
    /// Creates a new LiteralsMap capable of holding the information associated to `nb_variables`
    /// of type `T`.
    pub fn new(nb_vars: isize) -> LiteralsMap<T> {
        if nb_vars < 0 { panic!("It is impossible to have a problem with <0 variables"); }

        let nb_cells: usize = (1+ 2*nb_vars) as usize;

        unsafe {
            let buffer:*mut T = libc::malloc(nb_cells * mem::size_of::<T>()) as *mut T;
            let center:*mut T = buffer.offset(nb_vars);

            return LiteralsMap {
                nb_var: nb_vars as isize,
                buf   : center
            }
        }
    }

    /// Checks that `idx` respects the bounds of the array. Otherwise, it panics with an
    /// helpful message
    #[inline]
    fn check_bounds(&self, idx: isize) {
        if idx == 0 {
            panic!("Zero is not a valid literal. Hence it cannot be used as an index");
        }
        if idx < -self.nb_var || idx > self.nb_var {
            panic!("{} is not a valid literal index: the highest var id is {} ", idx, self.nb_var);
        }
    }
}

impl <T> Drop for LiteralsMap<T> {
    /// Whenever an LiteralsMap<T> is dropped, it frees the heap allocated buffer. However, nothing
    /// is done to free the objects that might be referenced by the buffer cells.
    fn drop(&mut self) {
        unsafe {
            let base_ptr = self.buf.offset(-self.nb_var) as *mut T;
            libc::free(base_ptr as *mut libc::c_void);
        }
    }
}


impl <T> Index<isize> for LiteralsMap<T> {
    type Output = T;

    /// A literal is identified by an integer. The given index is the literal id. Concretely, it is
    /// translated to a simple offset in the `buf`. Note though that this offset can be either
    /// positive or negative depending on the literal polarity. This function returns an *immutable*
    /// reference to the element associated with the given literal.
    #[inline]
    fn index(&self, lit:isize) -> &T {
        self.check_bounds(lit);
        unsafe {
            return self.buf.offset(lit).as_ref().unwrap();
        }
    }
}

impl <T> IndexMut<isize> for LiteralsMap<T> {
    /// A literal is identified by an integer. The given index is the literal id. Concretely, it is
    /// translated to a simple offset in the `buf`. Note though that this offset can be either
    /// positive or negative depending on the literal polarity. This function returns an *immutable*
    /// reference to the element associated with the given literal.
    #[inline]
    fn index_mut(&mut self, lit:isize) -> &mut T {
        self.check_bounds(lit);
        unsafe {
            return self.buf.offset(lit).as_mut().unwrap();
        }
    }
}


impl <T : fmt::Debug > fmt::Debug for LiteralsMap<T> {
    /// Provides a debug formatter for the LiteralsMap. This eases the debugging by showing the
    /// whole content of the map.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut res = String::from("LiteralsMap [ ");

        for i in 1..self.nb_var+1 {
            let pos_i =  i as isize;
            let neg_i = -i as isize;

            res.push_str(format!("\n    {:+06} -> {:?}", pos_i, self[pos_i]).as_str());
            res.push_str(format!("\n    {:+06} -> {:?}", neg_i, self[neg_i]).as_str());
        }

        res.push_str("\n]");
        return write!(f, "{}", res);
    }
}

/********************** UNIT TESTS FOR THE MODULE *************************************************/

#[cfg(test)]
mod test_array {
    use super::*;
    // an_array_cannot_have_zero_size is prevented by the compiler

    #[test]
    fn an_array_can_have_zero_size(){
        Array::<u32>::new(0);
    }

    #[test]
    fn array_index_can_be_zero(){
        let array = Array::<u32>::new(2);
        array[0];
    }

    #[test]
    fn array_index_can_be_positive(){
        let array = Array::<u32>::new(2);
        array[1];
    }

    /* ----------------------------------
     * should not even compile !
     * ----------------------------------
     * #[test]
     * #[should_panic]
     * fn array_index_cant_be_negative(){
     *     let array = Array::<u32>::new(2);
     *     array[-1];
     * }
     */

    #[test]
    #[should_panic]
    fn array_index_cant_go_out_of_bounds(){
        let array = Array::<u32>::new(2);
        array[2];
    }

    #[test]
    fn array_index_can_be_mutated_zero(){
        let mut array = Array::<u32>::new(2);
        array[0] = 42;

        assert_eq!(42, array[0]);
    }

    #[test]
    fn array_index_can_be_mutated_positive(){
        let mut array = Array::<u32>::new(2);
        array[1] = 42;

        assert_eq!(42, array[1]);
    }
}

#[cfg(test)]
mod test_literals_map {
    use super::*;
    // an_array_cannot_have_zero_size is prevented by the compiler

    #[test]
    fn lit_map_can_have_zero_size(){
        LiteralsMap::<u32>::new(0);
    }

    #[test]
    #[should_panic]
    fn lit_map_index_cant_be_zero(){
        let lit_map = LiteralsMap::<u32>::new(2);
        lit_map[0];
    }

    #[test]
    fn lit_map_index_can_be_positive(){
        let lit_map = LiteralsMap::<u32>::new(2);
        lit_map[1];
    }

    #[test]
    fn lit_map_index_can_be_negative(){
        let lit_map = LiteralsMap::<u32>::new(2);
        lit_map[-1];
    }

    #[test]
    fn lit_map_index_can_go_up_to_bound_positive(){
        let lit_map = LiteralsMap::<u32>::new(2);
        lit_map[2];
    }

    #[test]
    fn lit_map_index_can_go_up_to_bound_negative(){
        let lit_map = LiteralsMap::<u32>::new(2);
        lit_map[-2];
    }

    #[test]
    #[should_panic]
    fn lit_map_index_cant_go_out_of_bounds_positive(){
        let lit_map = LiteralsMap::<u32>::new(2);
        lit_map[3];
    }

    #[test]
    #[should_panic]
    fn lit_map_index_cant_go_out_of_bounds_negative(){
        let lit_map = LiteralsMap::<u32>::new(2);
        lit_map[-3];
    }

    #[test]
    fn lit_map_index_can_be_mutated_negative(){
        let mut lit_map = LiteralsMap::<u32>::new(2);
        lit_map[-1] = 42;

        assert_eq!(42, lit_map[-1]);
    }
    #[test]
    #[should_panic]
    fn lit_map_index_cant_be_mutated_zero(){
        let mut lit_map = LiteralsMap::<u32>::new(2);
        lit_map[ 0] = 42;
    }

    #[test]
    fn lit_map_index_can_be_mutated_positive(){
        let mut lit_map = LiteralsMap::<u32>::new(2);
        lit_map[1] = 42;

        assert_eq!(42, lit_map[1]);
    }
}