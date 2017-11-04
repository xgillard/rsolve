extern crate rsolve;

// set should turn some flag on
#[test]
fn set_should_turn_some_flag_on(){
    let mut x = Flags::new();

    assert!(! x.is_set(Flag::IsImplied) );
    assert!(! x.is_set(Flag::IsNotImplied) );
    assert!(! x.is_set(Flag::IsMarked) );
    assert!(! x.is_set(Flag::IsInConflictClause) );

    x.set(Flag::IsImplied);
    x.set(Flag::IsMarked);

    assert!(  x.is_set(Flag::IsImplied) );
    assert!(! x.is_set(Flag::IsNotImplied) );
    assert!(  x.is_set(Flag::IsMarked) );
    assert!(! x.is_set(Flag::IsInConflictClause) );
}

// unset should turn some flag off
#[test]
fn unset_should_turn_some_flag_off(){
    let mut x = Flags::new();

    assert!(! x.is_set(Flag::IsImplied) );
    assert!(! x.is_set(Flag::IsNotImplied) );
    assert!(! x.is_set(Flag::IsMarked) );
    assert!(! x.is_set(Flag::IsInConflictClause) );

    x.set(Flag::IsImplied);
    x.set(Flag::IsMarked);

    assert!(  x.is_set(Flag::IsImplied) );
    assert!(! x.is_set(Flag::IsNotImplied) );
    assert!(  x.is_set(Flag::IsMarked) );
    assert!(! x.is_set(Flag::IsInConflictClause) );

    x.unset(Flag::IsMarked);

    assert!(  x.is_set(Flag::IsImplied) );
    assert!(! x.is_set(Flag::IsNotImplied) );
    assert!(! x.is_set(Flag::IsMarked) );
    assert!(! x.is_set(Flag::IsInConflictClause) );

}
// reset should wipe everything off
#[test]
fn reset_should_wipe_everything_off(){
    let mut x = Flags::new();

    assert!(! x.is_set(Flag::IsImplied) );
    assert!(! x.is_set(Flag::IsNotImplied) );
    assert!(! x.is_set(Flag::IsMarked) );
    assert!(! x.is_set(Flag::IsInConflictClause) );

    x.set(Flag::IsImplied);
    x.set(Flag::IsMarked);

    assert!(  x.is_set(Flag::IsImplied) );
    assert!(! x.is_set(Flag::IsNotImplied) );
    assert!(  x.is_set(Flag::IsMarked) );
    assert!(! x.is_set(Flag::IsInConflictClause) );

    x.reset();
    assert!(! x.is_set(Flag::IsImplied) );
    assert!(! x.is_set(Flag::IsNotImplied) );
    assert!(! x.is_set(Flag::IsMarked) );
    assert!(! x.is_set(Flag::IsInConflictClause) );
}
// is_set should tell whether x is set
#[test]
fn is_set_should_tell_whether_some_flag_is_on(){
    let mut x = Flags::new();

    assert!(! x.is_set(Flag::IsImplied) );
    assert!(! x.is_set(Flag::IsNotImplied) );
    assert!(! x.is_set(Flag::IsMarked) );
    assert!(! x.is_set(Flag::IsInConflictClause) );

    x.set(Flag::IsImplied);
    x.set(Flag::IsMarked);

    assert!(  x.is_set(Flag::IsImplied) );
    assert!(! x.is_set(Flag::IsNotImplied) );
    assert!(  x.is_set(Flag::IsMarked) );
    assert!(! x.is_set(Flag::IsInConflictClause) );
}

// is_set should tell whether x is set
#[test]
fn one_of_should_tell_whether_some_flag_is_on(){
    let mut x = Flags::new();

    assert!(! x.is_set(Flag::IsImplied) );
    assert!(! x.is_set(Flag::IsNotImplied) );
    assert!(! x.is_set(Flag::IsMarked) );
    assert!(! x.is_set(Flag::IsInConflictClause) );

    x.set(Flag::IsImplied);
    x.set(Flag::IsMarked);

    assert!( x.one_of(Flag::IsImplied, Flag::IsNotImplied) );
    assert!( x.one_of(Flag::IsImplied, Flag::IsMarked) );
    assert!( x.one_of(Flag::IsImplied, Flag::IsInConflictClause) );

    assert!( x.one_of(Flag::IsMarked, Flag::IsImplied) );
    assert!( x.one_of(Flag::IsMarked, Flag::IsNotImplied) );
    assert!( x.one_of(Flag::IsMarked, Flag::IsInConflictClause) );

    assert!( x.one_of(Flag::IsNotImplied, Flag::IsImplied) );
    assert!( x.one_of(Flag::IsNotImplied, Flag::IsMarked) );
    assert!(!x.one_of(Flag::IsNotImplied, Flag::IsInConflictClause) );

    assert!( x.one_of(Flag::IsInConflictClause, Flag::IsImplied) );
    assert!( x.one_of(Flag::IsInConflictClause, Flag::IsMarked) );
    assert!(!x.one_of(Flag::IsInConflictClause, Flag::IsNotImplied) );
}

// |   should yield
#[test]
fn pipe_op_should_yield(){
    let x = Flags(0);

    assert_eq!( (x | Flag::IsMarked).0 , (Flags(Flag::IsMarked as u8)).0 );
}
// |=  shoudl mutate
#[test]
fn pipe_eq_op_should_mutate(){
    let mut x = Flags(0);
    x |= Flag::IsMarked;

    assert_eq!( x.0 , (Flags(Flag::IsMarked as u8)).0 );
}
// &   should yield
#[test]
fn and_op_should_yield(){
    let x = Flags(Flag::IsMarked as u8);
    assert_eq!( (x & Flag::IsMarked).0 , (Flags(Flag::IsMarked as u8)).0 );

    let x = Flags(Flag::IsImplied as u8);
    assert_eq!( (x & Flag::IsMarked).0 , 0_u8 );
}
// &=  should yield
#[test]
fn and_eq_op_should_mutate(){
    let mut x = Flags(Flag::IsMarked as u8);

    x &= Flag::IsMarked;
    assert_eq!( x.0 , Flag::IsMarked as u8 );

    x &= Flag::IsImplied;
    assert_eq!( x.0 , 0_u8 );
}
// ^   should yield
#[test]
fn xor_op_should_yield(){
    let x = Flags::new();
    assert_eq!( (x ^ Flag::IsMarked).0 , (Flags(Flag::IsMarked as u8)).0 );

    let x = Flags(Flag::IsImplied as u8);
    assert_eq!( (x ^ Flag::IsImplied).0 , 0_u8 );
}
// ^=  should mutate
#[test]
fn xor_eq_op_should_mutate(){
    let mut x = Flags::new();

    x ^= Flag::IsMarked;
    assert_eq!( x.0 , Flag::IsMarked as u8 );

    x ^= Flag::IsMarked;
    assert_eq!( x.0 , 0_u8 );
}

// debug ?