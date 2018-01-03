use std::io;
use std::io::*;

use core::*;
use solving::Solver;

pub fn parse_header<Source>(input : &mut Lines<Source>) -> Solver
    where Source : io::BufRead {

    for line in input {
        let line = line.unwrap();
        let line = line.trim();

        // it's a comment, skip it
        if line.starts_with("c ") { continue; }

        // it's the header, keep it
        if line.starts_with("p cnf ") {
            let mut tokens = line.split_whitespace();
            return Solver::new(tokens.nth(2).unwrap().parse::<usize>().unwrap());
        }
    }

    return Solver::new(0);
}

pub fn load_clauses<Source>(solver: &mut Solver, input: &mut Lines<Source>)
    where Source : io::BufRead {

    let mut ongoing_clause = vec![];
    for line in input {
        let line = line.unwrap();
        let line = line.trim();

        // it's a comment, skip it
        if line.starts_with("c ") { continue; }

        let tokens = line.split_whitespace();
        for token in tokens {
            let lit = token.parse::<iint>().unwrap();
            if lit != 0 {
                ongoing_clause.push(lit);
            } else {
                if solver.add_problem_clause(&mut ongoing_clause).is_err() {
                    return;
                }
                ongoing_clause.clear();
            }
        }
    }

    if !ongoing_clause.is_empty() {
        // Adds the very last clause (even if the last trailing zero is not present).
        // Note: the 'return' statement is useless, it only serves the point of using the result
        // of `solver.add_problem_clause()` and removing a compilation warning while doing so.
        if solver.add_problem_clause(&mut ongoing_clause).is_err() {
            return; /* actually, this means ignore the error: solver is in unsat = true mode. */
        }
    }

}