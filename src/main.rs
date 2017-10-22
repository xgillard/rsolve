extern crate rsolve;
use std::time::SystemTime;
use rsolve::*;
use rsolve::branching::*;

/*
fn main() {
    let     now = SystemTime::now();
    let    capa = 100_000_000;
    let mut ord = VariableOrdering::new(capa);

    for i in 1..capa+1 { ord.bump(Variable::from(i), i); }

    for _ in 1..capa+1 { ord.pop_top(); }

    println!("elapsed {:?}", SystemTime::now().duration_since(now).unwrap());
}
*/

use rsolve::utils::*;

use std::mem;
use std::rc::*;

// il ne compacte donc pas !
struct Xyz {
    x : bool,
    y : Bool,
    z : Sign
}

fn main(){

    let x = Aliasable::new(Clause::new(vec![Literal::from(-1)]));
    let a = x.alias();

    println!("x = {:?}", x);
    println!("a = {:?}", a);

    println!("Clause {}", mem::size_of::<Clause>() );
    println!("Aliasable {}", mem::size_of::<Aliasable<Clause>>() );
    println!("Alias {}", mem::size_of::<Alias<Clause>>() );
    println!("Sign {}", mem::size_of::<Sign>() );
    println!("Bool {}", mem::size_of::<Bool>() );
    println!("bool {}", mem::size_of::<bool>() );
    println!("Xyz {}", mem::size_of::<Xyz>() );
    println!("Rc {}", mem::size_of::<Rc<Clause>>() );

    println!("usize {}", mem::size_of::<usize>() );

}