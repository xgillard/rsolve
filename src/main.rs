extern crate rsolve;
use std::time::SystemTime;
use rsolve::*;
use rsolve::branching::*;

fn main() {
    let     now = SystemTime::now();
    let    capa = 100_000_000;
    let mut ord = VariableOrdering::new(capa);

    for i in 1..capa+1 { ord.bump(Variable::from(i), i); }

    for _ in 1..capa+1 { ord.pop_top(); }

    println!("elapsed {:?}", SystemTime::now().duration_since(now).unwrap());
}