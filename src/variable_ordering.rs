//! This file contains the implementation of an adaptable heap suitable to implement a VSIDS-like
//! variable ordering
use super::*;
use collections::VarIdxVec;
//use arrays::Array;

/// The variable ordering structure (aka the variable heap)
#[derive(Debug)]
pub struct VariableOrdering {
    /// A binary heap implemented as an array of variables
    heap: Vec<Variable>,
    /// The score associated with each element
    score   : VarIdxVec<uint>,
    /// The position of each id in the `heap` array
    position: VarIdxVec<uint>,
    /// The current size (#elements) in the heap
    size: uint,
    /// The capacity of the buffers
    capa: uint
}

impl VariableOrdering {
    /// Creates a new VariableOrdering heap capable with the given capacity. That is to say, one
    /// able to accept up to `capa` items.
    pub fn new(capa: uint) -> VariableOrdering {
        let mut ret = VariableOrdering {
            capa    : capa,
            size    : capa,
            heap    : Vec::with_capacity((1+capa) as usize),
            score   : VarIdxVec::with_capacity(capa as usize),
            position: VarIdxVec::with_capacity(capa as usize)
        };

        for i in 1..(capa+2) {
            ret.heap.push(Variable::from(i));
            ret.position.push(i);
            ret.score.push(i);
        }

        return ret;
    }

    /// return true iff there is no element left in the heap
    #[inline]
    pub fn is_empty(&self) -> bool {
        return self.size == 0;
    }

    /// updates the variable's score using microsat scoring scheme
    ///
    /// # Panics
    /// - if the given variable does not fit in the range [1 .. capa]
    #[inline]
    pub fn bump(&mut self, var: Variable, nb_conflicts: uint) {
        self.score[var] = (3*self.score[var] + (nb_conflicts<<5)) >> 2;

        if self.position[var] <= self.size { self.swim(var); }
    }

    /// Places the given `var` back in the heap (if not already present)
    ///
    /// # Panics
    /// - if the given variable does not fit in the range [1 .. capa]
    #[inline]
	pub fn push_back(&mut self, var: Variable) {
        let var_pos = self.position[var];

        // Do it iff it is not already present
        if var_pos > self.size {
            let other_pos = self.size +1;
            let other_var = self.heap[other_pos as usize];

            self.size                      += 1;
            self.heap[ var_pos   as usize ] = other_var;
            self.heap[ other_pos as usize ] = var;

            self.position[ other_var ] = var_pos;
            self.position[ var       ] = other_pos;

            self.swim(var);
        }
    }

	/// Removes the element with highest score from the heap and returns it.
	///
	/// # Return Value
	/// Returns the element with highest score on the heap.
	///
	/// # Panics
	/// - when one tries to pop an empty heap.
	#[inline]
    pub fn pop_top(&mut self) -> Variable {
        debug_assert!( !self.is_empty(), "Cannot pop from an empty heap");

        let var = self.heap[1];

        self.heap[1] = self.heap[self.size as usize];
        self.heap[self.size as usize] = var;

        self.position[ self.heap[1] ] = 1;
        self.position[ var ] = self.size;
        self.size -= 1;

        let new_head = self.heap[1];
        self.sink(new_head);

        return var;
    }

    /// Sinks the given variable down the heap until the moment when the heap
    /// invariant is restored.
    ///
    /// # Note
    /// This function assumes that `var` has already been sanity checked.
    #[inline]
    fn sink(&mut self, var: Variable) {
        let mut var_pos = self.position[var] as usize;
        let var_scr = self.score[var];

        let mut kid_pos = self.max_child_of(var_pos);
        let mut kid     = self.heap[kid_pos];
        let mut kid_scr = self.score[kid];

        while kid_pos != 0 && kid_scr > var_scr {
            self.heap[var_pos] = kid;
            self.position[kid] = var_pos as uint;

            var_pos = kid_pos;
            kid_pos = self.max_child_of(var_pos);
            kid     = self.heap [kid_pos];
            kid_scr = self.score[kid];
        }

        self.heap[var_pos] = var;
        self.position[var] = var_pos as uint;
    }

    /// Swims the given variable up the heap until the moment when the heap
    /// invariant is restored.
    ///
    /// # Note
    /// This function assumes that `var` has already been sanity checked.
    #[inline]
    fn swim(&mut self, var: Variable) {
        let mut var_pos = self.position[var] as usize;
        let var_scr = self.score   [var];

        let mut par_pos = var_pos >> 1;
        let mut par     = self.heap [par_pos];
        let mut par_scr = self.score[par    ];

        while par_pos > 0 && par_scr < var_scr {
            self.heap[var_pos] = par;
            self.position[par] = var_pos as uint;

            var_pos = par_pos;
            par_pos = par_pos >> 1;
            par     = self.heap [par_pos];
            par_scr = self.score[par    ];
        }

        self.heap[var_pos] = var;
        self.position[var] = var_pos as uint;
    }

    /// Returns the *position* of the next child to use while sinking
    /// down the item at position `pos`.
    ///
    /// # Params
    /// - pos the position of a node in the heap
    /// - the position of the child with the highest score or zero
    ///   when no such child exists.
    #[inline]
    fn max_child_of(&self, pos: usize) -> usize {
        let l_pos = pos << 1;
        let r_pos = l_pos +1;

        if l_pos > (self.size as usize) { return 0;    }
        if r_pos > (self.size as usize) { return l_pos;}

        let l_scr = self.score[ self.heap[l_pos] ];
        let r_scr = self.score[ self.heap[r_pos] ];

        return if l_scr > r_scr { l_pos } else { r_pos };
    }
}