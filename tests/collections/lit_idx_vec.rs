#[test]
fn with_capacity_preallocates_memory(){
    let v = LitIdxVec::<u8>::with_capacity(5);

    // granted, this feels weird !
    assert_eq!(v.capacity(), 10);
}

#[test]
fn push_values_interleaves_positive_and_negative(){
    let mut v = LitIdxVec::with_capacity(6);

    for i in 1..7 {
        v.push_values(i, -i);
    }

    assert_eq!("LitIdxVec([-1, 1, -2, 2, -3, 3, -4, 4, -5, 5, -6, 6])", format!("{:?}", v))
}

#[test]
fn push_init_interleaves_positive_and_negative(){
    let mut v = LitIdxVec::with_capacity(6);

    for i in 1..7 {
        let mut phase = 1;
        v.push_init(&mut || {
            let ret = i * phase;
            phase *= -1;
            return ret
        });
    }

    assert_eq!("LitIdxVec([-1, 1, -2, 2, -3, 3, -4, 4, -5, 5, -6, 6])", format!("{:?}", v))
}

#[test]
fn index_retrieves_the_right_info() {
    let mut v = LitIdxVec::with_capacity(100);

    for i in 1..101 {
        v.push_values(i, -i);
    }

    for i in 1..101 {
        assert_eq!( i, v[Literal::from( i)] );
        assert_eq!(-i, v[Literal::from(-i)] );
    }
}

#[test]
#[should_panic]
fn index_checks_lower_bound() {
    let mut v = LitIdxVec::with_capacity(6);

    for i in 1..7 {
        v.push_values(i, -i);
    }

    v[Literal::from(-12)];
}
#[test]
#[should_panic]
fn index_checks_upper_bound() {
    let mut v = LitIdxVec::with_capacity(6);

    for i in 1..7 {
        v.push_values(i, -i);
    }

    v[Literal::from(12)];
}

#[test]
fn index_mut_updates_the_right_value(){
    let mut v = LitIdxVec::with_capacity(6);

    for i in 1..7 {
        v.push_values(i, -i);
    }

    v[Literal::from( 2)] = 42;
    v[Literal::from(-2)] = 64;

    assert_eq!("LitIdxVec([-1, 1, 64, 42, -3, 3, -4, 4, -5, 5, -6, 6])", format!("{:?}", v))
}