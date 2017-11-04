extern crate rsolve;

use rsolve::core::*;
use rsolve::collections::*;

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