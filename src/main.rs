extern crate rsolve;

use rsolve::arrays::*;

fn main() {
    let mut a = LiteralsMap::<u32>::new(3);

    a[-1] = 3;
    a[-2] = 2;
    a[-3] = 1;
    a[ 1] = 3;
    a[ 2] = 2;
    a[ 3] = 1;
    println!("{:?}", a)
}