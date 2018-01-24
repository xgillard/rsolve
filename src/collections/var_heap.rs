use core::*;
use collections::VarIdxVec;

// -----------------------------------------------------------------------------------------------
/// # Variable Heap
/// A heap to efficiently order variables based on some (externally defined) scoring scheme
// -----------------------------------------------------------------------------------------------
#[derive(Debug)]
pub struct VarHeap {
    /// A binary heap implemented as an array of variables
    pub heap: Vec<Variable>,
    /// The score associated with each element
    pub score   : VarIdxVec<f64>,
    /// The position of each id in the `heap` array
    pub position: VarIdxVec<usize>,
    /// The current size (#elements) in the heap
    pub size: usize,
    /// The capacity of the buffers
    pub capa: usize
}

impl VarHeap {
    /// Creates a new heap with the given capacity.
    #[inline]
    pub fn new(capa: usize) -> VarHeap {
        let mut ret = VarHeap {
            capa    : capa,
            size    : capa,
            heap    : Vec::with_capacity(1+capa),
            score   : VarIdxVec::with_capacity(capa),
            position: VarIdxVec::with_capacity(capa)
        };

        // fill padding with a non-existing variable
        ret.heap.push(Variable::from(capa+1));

        // initialize the heap with actual values !
        for i in 1..(capa+1) {
            ret.heap.push(Variable::from(i));
            ret.position.push(i);
            ret.score.push(1.0);
        }

        // reclaim wastefully overallocated memory
        ret.heap    .shrink_to_fit();
        ret.position.shrink_to_fit();
        ret.score   .shrink_to_fit();

        return ret;
    }

    /// return true iff there is no element left in the heap
    #[inline]
    pub fn is_empty(&self) -> bool {
        return self.size == 0;
    }

    /// returns the number of variables currently in the heap
    #[inline]
    pub fn len(&self) -> usize { self.size }

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

    /// Returns the score associated with some given variable
    #[inline]
    pub fn get_score(&self, var: Variable) -> f64 {
        self.score[var]
    }

    /// Sinks the given variable down the heap until the moment when the heap
    /// invariant is restored.
    ///
    /// # Note
    /// This function assumes that `var` has already been sanity checked.
    #[inline]
    pub fn sink(&mut self, var: Variable) {
        let mut var_pos = self.position[var] as usize;
        let var_scr = self.score[var];

        let mut kid_pos = self.max_child_of(var_pos);
        let mut kid = self.heap[kid_pos]; // this might denote a non existing variable
        let mut kid_scr = if kid_pos != 0 { self.score[kid] } else { 0.0 };

        while kid_pos != 0 && kid_scr > var_scr {
            self.heap[var_pos] = kid;
            self.position[kid] = var_pos;

            var_pos = kid_pos;
            kid_pos = self.max_child_of(var_pos);
            kid     = self.heap [kid_pos];
            kid_scr = if kid_pos != 0 { self.score[kid] } else { 0.0 };
        }

        self.heap[var_pos] = var;
        self.position[var] = var_pos;
    }

    /// Swims the given variable up the heap until the moment when the heap
    /// invariant is restored.
    ///
    /// # Note
    /// This function assumes that `var` has already been sanity checked.
    #[inline]
    pub fn swim(&mut self, var: Variable) {
        let mut var_pos = self.position[var] as usize;
        let var_scr = self.score   [var];

        let mut par_pos = var_pos >> 1;
        let mut par= self.heap [par_pos];
        let mut par_scr = if par_pos != 0 { self.score[par] } else { 0.0 };

        while par_pos > 0 && par_scr < var_scr {
            self.heap[var_pos] = par;
            self.position[par] = var_pos;

            var_pos = par_pos;
            par_pos = par_pos >> 1;
            par     = self.heap [par_pos];
            par_scr = if par_pos != 0 { self.score[par] } else { 0.0 };
        }

        self.heap[var_pos] = var;
        self.position[var] = var_pos;
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


// -----------------------------------------------------------------------------------------------
/// # Unit Tests
// -----------------------------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;

    const MAX: usize = 100;

    #[test]
    fn test_new() {
        let result = VarHeap::new(1);
        eprintln!("{:#?}", result);
    }

    #[test]
    /// isEmpty is false as long as everything is not popped
    fn is_empty_remains_false_while_everything_wasnt_popped(){
        let mut tested = VarHeap::new(MAX);

        for _ in 1..MAX+1 {
            assert!( !tested.is_empty() );
            tested.pop_top();
        };

        assert!( tested.is_empty() );
    }

    /// isEmpty is false after a push back
    #[test]
    fn is_empty_is_false_after_push_back(){
        let mut tested = VarHeap::new(MAX);

        // make it empty
        for _ in 1..MAX+1 {
            tested.pop_top();
        }

        tested.push_back(Variable::from(4_usize));
        assert!( !tested.is_empty() );
    }


    #[test]
    #[should_panic]
    /// pushBack fails for zero
    fn push_back_must_fail_for_zero(){
        let mut tested = VarHeap::new(MAX);
        tested.push_back(Variable::from(0_usize));
    }

    #[test]
    /// pushBack has no effect if the item is already in the heap
    fn push_back_has_no_effect_when_already_on_heap(){
        let mut tested = VarHeap::new(MAX);
        // empty it
        for _ in 1..MAX+1 { tested.pop_top(); }
        // only 10 on heap
        tested.push_back(Variable::from(10_usize));
        tested.push_back(Variable::from(10_usize));

        assert_eq!(Variable::from(10_usize), tested.pop_top());
        assert!(tested.is_empty());
    }

    #[test]
    /// pushBack effectively insert the item at the right place in the heap
    fn push_back_must_effectively_put_item_back_on_the_heap(){
        let mut tested = VarHeap::new(MAX);
        // empty it
        for _ in 1..MAX+1 { tested.pop_top(); }
        // only 10 on heap
        tested.push_back(Variable::from(10_usize));

        assert!( !tested.is_empty());
        assert_eq!(Variable::from(10_usize), tested.pop_top());
        assert!(tested.is_empty());
    }

    #[test]
    /// pushBack effectively insert the item at the right place in the heap
    fn push_back_must_effectively_put_item_back_on_the_heap_2(){
        let mut tested = VarHeap::new(MAX);
        // empty it
        for _ in 1..MAX+1 { tested.pop_top(); }

        tested.score[Variable::from(2_usize)] =  6.0;
        tested.score[Variable::from(3_usize)] = 10.0;
        tested.score[Variable::from(7_usize)] = 14.0;
        tested.score[Variable::from(9_usize)] = 16.0;

        tested.push_back(Variable::from(7_usize));
        tested.push_back(Variable::from(3_usize));
        tested.push_back(Variable::from(9_usize));
        tested.push_back(Variable::from(2_usize));

        assert_eq!(tested.pop_top(),  Variable::from(9_usize));
        assert_eq!(tested.pop_top(),  Variable::from(7_usize));
        assert_eq!(tested.pop_top(),  Variable::from(3_usize));
        assert_eq!(tested.pop_top(),  Variable::from(2_usize));
        assert_eq!(tested.is_empty(), true);
    }

    #[test]
    #[should_panic]
    fn pop_top_must_fail_on_empty_heap(){
        let mut tested = VarHeap::new(MAX);
        // empty it
        for _ in 1..MAX+1 { tested.pop_top(); }
        // should fail
        tested.pop_top();
    }

    #[test]
    fn pop_top_must_remove_items_in_decreasing_score_order(){
        let mut tested = VarHeap::new(MAX);

        for i in 1..MAX+1 {
            let v = Variable::from(i);
            tested.score[v] = (MAX + i) as f64 ;
            tested.swim(v);
        }

        let mut last = usize::max_value();
        for i in 0..MAX {
            let popped = tested.pop_top();
            assert_eq!(popped, Variable::from(MAX-i));
            assert!   (usize::from(popped) < last);
            last = popped.into();
        }
    }

    #[test]
    fn get_score_should_return_the_score_of_some_given_variable() {
        let mut tested = VarHeap::new(MAX);

        for i in 1..1+MAX {
            assert_eq!(1.0, tested.get_score(var(i as u32)));
        }

        tested.score[var(3)] = 2.0;
        tested.swim(var(3));

        assert_eq!(2.0, tested.get_score(var(3)));
    }
}