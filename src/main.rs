extern crate rsolve;

use std::io::*;
use rsolve::*;

// TODO: Solver.rs -> test nb_unassigned(), is_locked() et reduce_db()
// TODO: dimacs.rs -> *
// TODO: supporter plus de types d'input
// TODO: supporter plus d'options DRUP, print_model
// TODO: etre plus intelligent (LRB, inprocessing, partial restarts)
// TODO: etre plus bas niveau avec mes alias
// TODO: tests d'intégration
fn main() {
    let stdin = stdin();
    let lock = stdin.lock();
    let mut lines = lock.lines();
    let mut solver = parse_header(&mut lines);

    load_clauses(&mut solver, &mut lines);

    let satisfiable = solver.solve();

    if satisfiable {
        println!("s SATISFIABLE");
    } else {
        println!("s UNSATISFIABLE");
    }
}