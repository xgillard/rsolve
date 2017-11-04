extern crate rsolve;

use rsolve::*;
use rsolve::variable_ordering::*;

const MAX: uint = 100;

#[test]
fn test_new() {
    let result = VariableOrdering::new(1);
    eprintln!("{:#?}", result);
}

#[test]
/// isEmpty is false as long as everything is not popped
fn is_empty_remains_false_while_everything_wasnt_popped(){
    let mut tested = VariableOrdering::new(MAX);

    for _ in 1..MAX+1 {
        assert!( !tested.is_empty() );
        tested.pop_top();
    };

    assert!( tested.is_empty() );
}

/// isEmpty is false after a push back
#[test]
fn is_empty_is_false_after_push_back(){
    let mut tested = VariableOrdering::new(MAX);

    // make it empty
    for _ in 1..MAX+1 {
        tested.pop_top();
    }

    tested.push_back(Variable::from(4));
    assert!( !tested.is_empty() );
}

#[test]
#[should_panic]
/// bump fails for zero
fn bump_must_fail_for_zero(){
    let mut tested = VariableOrdering::new(MAX);

    tested.bump(Variable::from(0), 1);
}

#[test]
#[should_panic]
/// bump fails above the max
fn bump_must_fail_above_the_max() {
    let mut tested = VariableOrdering::new(MAX);
    // because the ordering can hold up to MAX variables, it means that the accepted vars
    // range from [1;MAX+1]. Hence, to get out of bounds, we need to use MAX+2.
    tested.bump(Variable::from(MAX+2), 1);
}

#[test]
/// bump changes the score, and adapts the position
fn bump_must_update_the_score_and_position(){
    let mut tested = VariableOrdering::new(MAX);
    tested.bump(Variable::from(50), 40);

    assert_eq!( tested.pop_top(), Variable::from(50));
}

#[test]
/// bump wont push back an item that has already been popped
fn bump_wont_push_back_an_item_that_has_been_popped(){
    let mut tested = VariableOrdering::new(MAX);
    // empty it
    for _ in 1..MAX+1 { tested.pop_top(); }

    assert!(tested.is_empty());
    tested.bump(Variable::from(42), 100);
    assert!(tested.is_empty());
}

#[test]
/// bump wont reactivate a popped item
fn bump_wont_let_an_item_that_has_been_popped_sneak_into_the_active_ones(){
    let mut tested = VariableOrdering::new(MAX);
    // empty it
    for _ in 1..MAX+1 { tested.pop_top(); }

    assert!(tested.is_empty());
    tested.push_back(Variable::from(5));
    tested.bump(Variable::from(42), 1000);
    assert_eq!(tested.pop_top(), Variable::from(5));
    assert!(tested.is_empty());
}

#[test]
/// Bump updates the score even when item is popped
fn bump_updates_score_even_when_item_is_popped(){
    let mut tested = VariableOrdering::new(MAX);
    // empty it
    for _ in 1..MAX+1 { tested.pop_top(); }

    //assert!(tested.is_empty());
    tested.bump(Variable::from(42), 1000);
    assert!(tested.is_empty());

    // refill it
    for i in 1..MAX+1 { tested.push_back(Variable::from(i)); }

    assert_eq!(tested.pop_top(), Variable::from(42));
}

#[test]
#[should_panic]
/// pushBack fails for zero
fn push_back_must_fail_for_zero(){
    let mut tested = VariableOrdering::new(MAX);
    tested.push_back(Variable::from(0));
}

#[test]
/// pushBack has no effect if the item is already in the heap
fn push_back_has_no_effect_when_already_on_heap(){
    let mut tested = VariableOrdering::new(MAX);
    // empty it
    for _ in 1..MAX+1 { tested.pop_top(); }
    // only 10 on heap
    tested.push_back(Variable::from(10));
    tested.push_back(Variable::from(10));

    assert_eq!(Variable::from(10), tested.pop_top());
    assert!(tested.is_empty());
}

#[test]
/// pushBack effectively insert the item at the right place in the heap
fn push_back_must_effectively_put_item_back_on_the_heap(){
    let mut tested = VariableOrdering::new(MAX);
    // empty it
    for _ in 1..MAX+1 { tested.pop_top(); }
    // only 10 on heap
    tested.push_back(Variable::from(10));

    assert!( !tested.is_empty());
    assert_eq!(Variable::from(10), tested.pop_top());
    assert!(tested.is_empty());
}

#[test]
/// pushBack effectively insert the item at the right place in the heap
fn push_back_must_effectively_put_item_back_on_the_heap_2(){
    let mut tested = VariableOrdering::new(MAX);
    // empty it
    for _ in 1..MAX+1 { tested.pop_top(); }

    tested.bump(Variable::from(7), 7);
    tested.bump(Variable::from(3), 3);
    tested.bump(Variable::from(9), 9);
    tested.bump(Variable::from(2), 2);

    tested.push_back(Variable::from(7));
    tested.push_back(Variable::from(3));
    tested.push_back(Variable::from(9));
    tested.push_back(Variable::from(2));

    assert_eq!(tested.pop_top(),  Variable::from(9));
    assert_eq!(tested.pop_top(),  Variable::from(7));
    assert_eq!(tested.pop_top(),  Variable::from(3));
    assert_eq!(tested.pop_top(),  Variable::from(2));
    assert_eq!(tested.is_empty(), true);
}

#[test]
#[should_panic]
fn pop_must_fail_on_empty_heap(){
    let mut tested = VariableOrdering::new(MAX);
    // empty it
    for _ in 1..MAX+1 { tested.pop_top(); }
    // should fail
    tested.pop_top();
}

#[test]
fn pop_top_must_remove_items_in_decreasing_score_order(){
    let mut tested = VariableOrdering::new(MAX);
    for i in 1..MAX+1 { tested.bump(Variable::from(i), i); }

    let mut last = usize::max_value();
    for i in 0..MAX {
        let popped = tested.pop_top();
        assert_eq!(popped, Variable::from(MAX-i));
        assert!   (popped.to_usize() < last);
        last = popped.to_usize();
    }
}