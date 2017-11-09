extern crate rsolve;

use std::io::*;
use rsolve::*;

// TODO: Solver.rs -> test reduce_db()
// TODO: dimacs.rs -> *
// TODO: etre plus intelligent (LRB, inprocessing, partial restarts)
// TODO: supporter plus d'options DRUP, print_model
// TODO: supporter plus de types d'input
// TODO: etre plus bas niveau avec mes alias
fn main() {
    print_header();
    let stdin = stdin();
    let lock = stdin.lock();
    let mut lines = lock.lines();
    let mut solver = parse_header(&mut lines);

    load_clauses(&mut solver, &mut lines);

    let satisfiable = solver.solve();

    print_result(&solver, satisfiable);
}

fn print_header() {
    println!("c *************************************************************************");
    println!("c This is the `rsolve` SAT solver version 0.1.0");
    println!("c -------------------------------------------------------------------------");
    println!("c Copyright 2017 Xavier Gillard, Université Catholique de Louvain");
    println!("c This software is licensed to you under the terms of the MIT license");
    println!("c =========================================================================");
}

fn print_result(solver: &Solver, satisfiable: bool){
    if satisfiable {
        println!("s SATISFIABLE");
    } else {
        println!("s UNSATISFIABLE");
    }
    println!("c -------------------------------------------------------------------------");
    println!("c nb_conflicts {}", solver.nb_conflicts);
    println!("c nb_restarts  {}", solver.nb_restarts);
    println!("c *************************************************************************");
}