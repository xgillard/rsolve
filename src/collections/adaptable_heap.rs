//! This file contains the implementation of an adaptable heap suitable to implement variable
//! ordering heuristics.
use std::marker::Copy;
use std::convert::{From, Into};
use std::cmp::PartialOrd;

// -----------------------------------------------------------------------------------------------
/// # Adaptable Binary Heap
/// A binary heap where the score of items can be updated.
// -----------------------------------------------------------------------------------------------
#[derive(Debug)]
pub struct AdaptableBinaryHeap<Item, Score>
    where Item : Copy + From<usize> + Into<usize>,
          Score: Copy + Default     + PartialOrd
{
    /// A binary heap implemented as an array of items
    heap: Vec<Item>,
    /// The score associated with each element
    score: Vec<Score>,
    /// The position of each id in the `heap` array
    position: Vec<usize>,
    /// The current size (#elements) in the heap
    size: usize,
    /// The capacity of the buffers
    capa: usize
}

impl<Item, Score> AdaptableBinaryHeap<Item, Score>
    where Item : Copy + From<usize> + Into<usize>,
          Score: Copy + Default     + PartialOrd
{
    /// Creates a new AdaptableBinaryHeap heap with the given capacity. That is to say, one
    /// able to accept up to `capa` items.
    ///
    /// # Note
    /// It is important that all accepted values of items map to an integer between 1 and capa.
    ///
    pub fn new(capa: usize) -> AdaptableBinaryHeap<Item, Score> {
        let dummy = Item::from(capa+1);

        let mut ret : AdaptableBinaryHeap<Item, Score> = AdaptableBinaryHeap {
            capa    : capa,
            size    : capa,
            heap    : vec![dummy           ; 1+capa],
            score   : vec![Score::default(); 1+capa],
            position: vec![0               ; 1+capa]
        };

        // fill padding with a dummy item
        ret.heap[0] = dummy;

        // initialize the heap with actual values !
        for i in 1..(capa+1) {
            ret.heap[i] = Item::from(i);
            ret.position[i] = i;
        }

        return ret;
    }

    /// return true iff there is no element left in the heap
    #[inline]
    pub fn is_empty(&self) -> bool { return self.size == 0; }

    /// Places the given `itm` back in the heap (if not already present)
    ///
    /// # Panics
    /// - if the given item does not fit in the range [1 .. capa]
    #[inline]
    pub fn push_back(&mut self, itm: Item) {
        assert!(0 < itm.into() && self.capa >= itm.into(), format!("`itm` be in the range [0;{}]", self.capa) );

        let itm_pos = self.position[itm.into()];

        // Do it iff it is not already present
        if itm_pos > self.size {
            let other_pos = self.size +1;
            let other_itm = self.heap[other_pos];

            self.size                 += 1;
            self.heap[ itm_pos       ] = other_itm;
            self.heap[ other_pos     ] = itm;

            self.position[ other_itm.into() ] = itm_pos;
            self.position[ itm.into()       ] = other_pos;

            self.swim(itm);
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
    pub fn pop_top(&mut self) -> Item {
        debug_assert!( !self.is_empty(), "Cannot pop from an empty heap");

        let itm = self.heap[1];

        self.heap[1] = self.heap[self.size];
        self.heap[self.size] = itm;

        self.position[ self.heap[1].into() ] = 1;
        self.position[ itm.into() ] = self.size;
        self.size -= 1;

        let new_head = self.heap[1];
        self.sink(new_head);

        return itm;
    }

    /// Returns the score associated with some given item
    #[inline]
    pub fn get_score(&self, itm: Item) -> Score {
        assert!(0 < itm.into() && self.capa >= itm.into(), format!("`itm` be in the range [0;{}]", self.capa) );
        self.score[itm.into()]
    }

    /// Updates the score associated with some given item
    #[inline]
    pub fn set_score(&mut self, itm: Item, score: Score) {
        assert!(0 < itm.into() && self.capa >= itm.into(), format!("`itm` be in the range [0;{}]", self.capa) );
        self.score[itm.into()] = score;

        if self.position[itm.into()] <= self.size { self.swim(itm); }
    }

    /// Sinks the given item down the heap until the moment when the heap
    /// invariant is restored.
    ///
    /// # Note
    /// This function assumes that `itm` has already been sanity checked.
    #[inline]
    fn sink(&mut self, itm: Item) {
        let mut itm_pos = self.position[itm.into()] as usize;
        let itm_scr = self.score[itm.into()];

        let mut kid_pos = self.max_child_of(itm_pos);
        let mut kid = self.heap[kid_pos]; // this might denote a dummy item
        let mut kid_scr = if kid_pos != 0 { self.score[kid.into()] } else { Score::default() };

        while kid_pos != 0 && kid_scr > itm_scr {
            self.heap[itm_pos]        = kid;
            self.position[kid.into()] = itm_pos;

            itm_pos = kid_pos;
            kid_pos = self.max_child_of(itm_pos);
            kid     = self.heap [kid_pos];
            kid_scr = if kid_pos != 0 { self.score[kid.into()] } else { Score::default() };
        }

        self.heap[itm_pos]        = itm;
        self.position[itm.into()] = itm_pos;
    }

    /// Swims the given item up the heap until the moment when the heap
    /// invariant is restored.
    ///
    /// # Note
    /// This function assumes that `itm` has already been sanity checked.
    #[inline]
    fn swim(&mut self, itm: Item) {
        let mut itm_pos = self.position[itm.into()];
        let itm_scr = self.score[itm.into()];

        let mut par_pos = itm_pos >> 1;
        let mut par= self.heap [par_pos];
        let mut par_scr = if par_pos != 0 { self.score[par.into()] } else { Score::default() };

        while par_pos > 0 && par_scr < itm_scr {
            self.heap[itm_pos       ] = par;
            self.position[par.into()] = par_pos;

            itm_pos = par_pos;
            par_pos = par_pos >> 1;
            par     = self.heap [par_pos];
            par_scr = if par_pos != 0 { self.score[par.into()] } else { Score::default() };
        }

        self.heap[itm_pos       ] = itm;
        self.position[itm.into()] = itm_pos;
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

        if l_pos > self.size { return 0;    }
        if r_pos > self.size { return l_pos;}

        let l_scr = self.score[ self.heap[l_pos].into() ];
        let r_scr = self.score[ self.heap[r_pos].into() ];

        return if l_scr > r_scr { l_pos } else { r_pos };
    }
}

// -----------------------------------------------------------------------------------------------
/// # Unit Tests
// -----------------------------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;
    use core::*;

    const MAX : usize = 100;

    #[test]
    fn test_new() {
        let result = AdaptableBinaryHeap::<Variable, usize>::new(1);
        eprintln!("{:#?}", result);
    }

    #[test]
    /// isEmpty is false as long as everything is not popped
    fn is_empty_remains_false_while_everything_wasnt_popped(){
        let mut tested = AdaptableBinaryHeap::<Variable, usize>::new(MAX);

        for _ in 1..MAX+1 {
            assert!( !tested.is_empty() );
            tested.pop_top();
        };

        assert!( tested.is_empty() );
    }

    /// isEmpty is false after a push back
    #[test]
    fn is_empty_is_false_after_push_back(){
        let mut tested = AdaptableBinaryHeap::<Variable, usize>::new(MAX);

        // make it empty
        for _ in 1..MAX+1 {
            tested.pop_top();
        }

        tested.push_back(Variable::from(4_usize));
        assert!( !tested.is_empty() );
    }

    #[test]
    #[should_panic]
    fn set_score_must_fail_for_zero(){
        let mut tested = AdaptableBinaryHeap::<usize, usize>::new(MAX);

        tested.set_score(0, 42);
    }

    #[test]
    #[should_panic]
    fn set_score_must_fail_above_the_max() {
        let mut tested = AdaptableBinaryHeap::<usize, usize>::new(MAX);
        // because the ordering can hold up to MAX variables, it means that the accepted vars
        // range from [1;MAX+1]. Hence, to get out of bounds, we need to use MAX+2.
        tested.set_score(MAX+2, 42);
    }

    #[test]
    fn set_score_must_update_the_score_and_position(){
        let mut tested = AdaptableBinaryHeap::<Variable, usize>::new(MAX);
        tested.set_score(Variable::from(50_usize), 42);

        assert_eq!( tested.pop_top(), Variable::from(50_usize));
    }

    #[test]
    fn set_score_wont_push_back_an_item_that_has_been_popped(){
        let mut tested = AdaptableBinaryHeap::<Variable, usize>::new(MAX);
        // empty it
        for _ in 1..MAX+1 { tested.pop_top(); }

        assert!(tested.is_empty());
        tested.set_score(Variable::from(42_usize), 42);
        assert!(tested.is_empty());
    }

    #[test]
    fn set_score_wont_let_an_item_that_has_been_popped_sneak_into_the_active_ones(){
        let mut tested = AdaptableBinaryHeap::<Variable, usize>::new(MAX);
        // empty it
        for _ in 1..MAX+1 { tested.pop_top(); }

        assert!(tested.is_empty());
        tested.push_back(Variable::from(5_usize));
        tested.set_score(Variable::from(42_usize), 43);
        assert_eq!(tested.pop_top(), Variable::from(5_usize));
        assert!(tested.is_empty());
    }

    #[test]
    fn set_score_updates_score_even_when_item_is_popped(){
        let mut tested = AdaptableBinaryHeap::<Variable, usize>::new(MAX);
        // empty it
        for _ in 1..MAX+1 { tested.pop_top(); }

        //assert!(tested.is_empty());
        tested.set_score(Variable::from(42_u32), 42);
        assert!(tested.is_empty());

        // refill it
        for i in 1..MAX+1 { tested.push_back(Variable::from(i)); }

        assert_eq!(tested.pop_top(), Variable::from(42_usize));
    }

    #[test]
    #[should_panic]
    /// pushBack fails for zero
    fn push_back_must_fail_for_zero(){
        let mut tested = AdaptableBinaryHeap::<Variable, usize>::new(MAX);
        tested.push_back(Variable::from(0_usize));
    }

    #[test]
    /// pushBack has no effect if the item is already in the heap
    fn push_back_has_no_effect_when_already_on_heap(){
        let mut tested = AdaptableBinaryHeap::<Variable, usize>::new(MAX);
        // empty it
        for _ in 1..MAX+1 { tested.pop_top(); }
        // only 10 on heap
        tested.push_back(Variable::from(10_u32));
        tested.push_back(Variable::from(10_u32));

        assert_eq!(Variable::from(10_u32), tested.pop_top());
        assert!(tested.is_empty());
    }

    #[test]
    /// pushBack effectively insert the item at the right place in the heap
    fn push_back_must_effectively_put_item_back_on_the_heap(){
        let mut tested = AdaptableBinaryHeap::<Variable, usize>::new(MAX);
        // empty it
        for _ in 1..MAX+1 { tested.pop_top(); }
        // only 10 on heap
        tested.push_back(Variable::from(10_u32));

        assert!( !tested.is_empty());
        assert_eq!(Variable::from(10_u32), tested.pop_top());
        assert!(tested.is_empty());
    }

    #[test]
    /// pushBack effectively insert the item at the right place in the heap
    fn push_back_must_effectively_put_item_back_on_the_heap_2(){
        let mut tested = AdaptableBinaryHeap::<Variable, usize>::new(MAX);
        // empty it
        for _ in 1..MAX+1 { tested.pop_top(); }

        tested.set_score(Variable::from(2_u32), 1);
        tested.set_score(Variable::from(3_u32), 2);
        tested.set_score(Variable::from(7_u32), 3);
        tested.set_score(Variable::from(9_u32), 4);

        tested.push_back(Variable::from(7_u32));
        tested.push_back(Variable::from(3_u32));
        tested.push_back(Variable::from(9_u32));
        tested.push_back(Variable::from(2_u32));

        assert_eq!(tested.pop_top(),  Variable::from(9_u32));
        assert_eq!(tested.pop_top(),  Variable::from(7_u32));
        assert_eq!(tested.pop_top(),  Variable::from(3_u32));
        assert_eq!(tested.pop_top(),  Variable::from(2_u32));
        assert_eq!(tested.is_empty(), true);
    }

    #[test]
    #[should_panic]
    fn pop_top_must_fail_on_empty_heap(){
        let mut tested = AdaptableBinaryHeap::<Variable, usize>::new(MAX);
        // empty it
        for _ in 1..MAX+1 { tested.pop_top(); }
        // should fail
        tested.pop_top();
    }

    #[test]
    fn pop_top_must_remove_items_in_decreasing_score_order(){
        let mut tested = AdaptableBinaryHeap::<Variable, usize>::new(MAX);
        for i in 1..MAX+1 {
            tested.set_score(Variable::from(i), i);
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
    fn get_score_should_return_the_score_of_some_given_item() {
        let mut tested = AdaptableBinaryHeap::<Variable, usize>::new(MAX);

        for i in 1..1+MAX {
            assert_eq!(usize::default(), tested.get_score(Variable::from(i)));
        }

        tested.set_score(var(3), 2);
        assert_eq!(2, tested.get_score(var(3)));
    }
}