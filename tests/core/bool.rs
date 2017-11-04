extern crate rsolve;

use rsolve::core::bool::*;

#[test]
fn to_i8(){
    assert_eq!(-1, Bool::False.to_i8());
    assert_eq!( 1, Bool::True .to_i8());
    assert_eq!( 0, Bool::Undef.to_i8());
}

#[test]
fn eq() {
    assert_eq!(Bool::True , Bool::True );
    assert_ne!(Bool::True , Bool::False);
    assert_ne!(Bool::True , Bool::Undef);

    assert_eq!(Bool::False, Bool::False );
    assert_ne!(Bool::False, Bool::True );
    assert_ne!(Bool::False, Bool::Undef);

    assert_eq!(Bool::Undef, Bool::Undef );
    assert_ne!(Bool::Undef, Bool::True );
    assert_ne!(Bool::Undef, Bool::False);
}

#[test]
fn not(){
    assert_eq!(! Bool::True , Bool::False);
    assert_eq!(! Bool::False, Bool::True );
    assert_eq!(! Bool::Undef, Bool::Undef);
}