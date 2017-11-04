extern crate rsolve;

use rsolve::core::*;

#[test]
#[should_panic]
fn from_should_fail_on_zero() {
    assert_eq!("Variable(0)", format!("{:?}", var(0)));
}

// negatives are caught by the compiler

#[test]
fn from_should_work_on_positive_number() {
    assert_eq!("Variable(42)", format!("{:?}", var(42)));
}

#[test]
fn to_usize_should_return_raw_value() {
    assert_eq!(42, var(42).to_usize());
}

#[test]
fn test_equals_is_true_for_same_values() {
    assert_eq!(var(42), var(42));
}
#[test]
fn test_equals_is_false_for_different_values() {
    assert_ne!(var(5), var(42));
}