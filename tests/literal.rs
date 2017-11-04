extern crate rsolve;

use rsolve::core::*;

#[test]
#[should_panic]
fn constructor_fails_for_zero(){
    Literal::from(0);
}

#[test]
fn constructor_work_for_positive(){
    assert_eq!("Literal(1)", format!("{:?}", Literal::from(1)));
}
#[test]
fn constructor_work_for_negative(){
    assert_eq!("Literal(-1)", format!("{:?}", Literal::from(-1)));
}
#[test]
fn constructor_work_for_var(){
    assert_eq!("Literal(1)", format!("{:?}", Literal::from_var(var(1), Sign::Positive)));
    assert_eq!("Literal(-1)", format!("{:?}", Literal::from_var(var(1), Sign::Negative)));
}
#[test]
fn positive_builds_positive_lit(){
    assert_eq!("Literal(1)", format!("{:?}", Literal::positive(var(1))));
}
#[test]
fn negative_builds_negative_lit(){
    assert_eq!("Literal(-1)", format!("{:?}", Literal::negative(var(1))));
}
#[test]
fn var_returns_the_original_var(){
    let v = var(42);

    assert_eq!(v, Literal::positive(v).var());
    assert_eq!(v, Literal::negative(v).var());
}
#[test]
fn sign_is_positive_for_positive_lits(){
    let v = var(42);

    if let Sign::Positive = Literal::positive(v).sign() {
        assert!(true);
    } else {
        panic!("Should have been positive")
    }
}
#[test]
fn sign_is_negative_for_negative_lits(){
    let v = var(42);

    if let Sign::Negative = Literal::negative(v).sign() {
        assert!(true);
    } else {
        panic!("Should have been negative")
    }
}
#[test]
fn to_isize_should_return_raw_value() {
    assert_eq!(-42, Literal::from(-42).to_isize());
}

#[test]
fn test_equality() {
    let a = Literal::from(-1);
    let b = Literal::negative(var(1));
    let c = Literal::from_var(var(1), Sign::Negative);

    // reflexive
    assert_eq!(a, a);
    // transitive
    assert_eq!(a, b);
    assert_eq!(b, c);
    assert_eq!(a, c);
    // symmetric
    assert_eq!(a, b);
    assert_eq!(b, a);
}

#[test]
fn test_neg(){
    let a = Literal::from(-1);
    let b = Literal::positive(var(1));
    let c = Literal::from_var(var(1), Sign::Positive);

    assert_eq!(a, --a);
    assert_eq!(a, -b);
    assert_eq!(a, -c);
}
#[test]
fn test_not(){
    let a = Literal::from(-1);
    let b = Literal::positive(var(1));
    let c = Literal::from_var(var(1), Sign::Positive);

    assert_eq!(a, !!a);
    assert_eq!(a, !b);
    assert_eq!(a, !c);

    assert_ne!(a, !a);
    assert_ne!(a, b);
    assert_ne!(a, c);

    assert_ne!(a, Literal::from(32));
    assert_ne!(a, Literal::from(-32));
}