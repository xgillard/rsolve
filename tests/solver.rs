extern crate rsolve;

use rsolve::core::*;
use rsolve::flags::*;
use rsolve::solver::*;

#[test]
fn propagate_processes_everything_until_a_fixed_point_is_reached(){
    let mut solver = Solver::new(3);

    // initialize the constraint database
    solver.add_problem_clause(vec![1, -2, -3]);
    solver.add_problem_clause(vec![2, -3]);
    solver.add_problem_clause(vec![3]);

    // start the test (for real !)
    solver.assign(Literal::from(3), None).expect("3 should be assignable");

    assert_eq!(solver.trail.propagated, 0);
    assert_eq!(solver.trail.prop_queue, vec![lit(-3)]);

    assert!(solver.propagate().is_none());

    assert_eq!(solver.trail.propagated, 3);
    assert_eq!(solver.trail.prop_queue, vec![lit(-3), lit(-2), lit(-1)]);
}

#[test]
fn propagate_stops_when_a_conflict_is_detected() {
    let mut solver = Solver::new(3);

    // initialize the constraint database
    solver.add_problem_clause(vec![ 1, -2, -3]);
    solver.add_problem_clause(vec![ 2, -3]);
    solver.add_problem_clause(vec![ 3]);
    solver.add_problem_clause(vec![-2]);

    // start the test (for real !)
    solver.assign(Literal::from( 3), None).expect(" 3 should be assignable");
    // if I propagated here, then -2 shouldn't be assignable anymore
    solver.assign(Literal::from(-2), None).expect("-2 should be assignable");

    let conflict = solver.propagate();
    assert_eq!("Some(Alias(Some(Clause([Literal(2), Literal(-3)]))))", format!("{:?}", conflict));
    assert_eq!(solver.trail.prop_queue, vec![lit(-3), lit(2)])
}

#[test]
fn propagate_finds_a_non_trivial_conflict(){
    /*-
     * a ------------------------------------/--- c
     *                                      /
     *     /------- e ---- f --- -b --- -h +
     *    /                    /           \
     * d /-- g ---------------/             \--- -c
     *
     */
    let mut solver = Solver::new(8);
    solver.add_problem_clause(vec![ 1,-8, 3]); // c0
    solver.add_problem_clause(vec![ 1, 4,-5]); // c1
    solver.add_problem_clause(vec![ 5,-6, 7]); // c2
    solver.add_problem_clause(vec![ 6, 2, 7]); // c3
    solver.add_problem_clause(vec![ 4,-7]);    // c4
    solver.add_problem_clause(vec![-2, 8]);    // c5
    solver.add_problem_clause(vec![-8,-3]);    // c6

    assert_eq!(Ok(()), solver.assign(lit(-1), None));
    assert_eq!(Ok(()), solver.assign(lit(-4), None));

    let conflict = solver.propagate();
    assert!(conflict.is_some());
    assert_eq!(format!("{:?}", solver.constraints[0].alias()),
               format!("{:?}", conflict.unwrap()));
}

// isUIP must be true when the literal is a decision
#[test]
fn is_uip_must_be_true_when_literal_is_a_decision() {
    let mut solver = Solver::new(8);

    solver.assign(lit(2), None).expect("2 must be assignable");
    solver.assign(lit(4), None).expect("4 must be assignable");
    solver.assign(lit(8), None).expect("8 must be assignable");

    assert!(solver.is_uip(0));
    assert!(solver.is_uip(1));
    assert!(solver.is_uip(2));
}

// isUIP must be true when there is no other marked literal before next decision
#[test]
fn is_uip_must_be_true_when_there_is_no_other_marked_literal_before_next_decision(){
    /*-
     * a ------------------------------------/--- c
     *                                      /
     *     /------- e ---- f --- -b --- -h +
     *    /                    /           \
     * d /-- g ---------------/             \--- -c
     *
     */
    let mut solver = Solver::new(8);
    solver.add_problem_clause(vec![ 1,-8, 3]); // c0
    solver.add_problem_clause(vec![ 1, 4,-5]); // c1
    solver.add_problem_clause(vec![ 5,-6, 7]); // c2
    solver.add_problem_clause(vec![ 6, 2, 7]); // c3
    solver.add_problem_clause(vec![ 4,-7]);    // c4
    solver.add_problem_clause(vec![-2, 8]);    // c5
    solver.add_problem_clause(vec![-8,-3]);    // c6

    assert_eq!(Ok(()), solver.assign(lit(-1), None));
    assert_eq!(Ok(()), solver.assign(lit(-4), None));

    let conflict = solver.propagate();

    assert!(conflict.is_some());
    assert_eq!("Some(Alias(Some(Clause([Literal(3), Literal(-8), Literal(1)]))))",
               format!("{:?}", &conflict));
    assert_eq!(6, solver.find_first_uip(conflict.unwrap().get_ref().unwrap()));
    // note: is_uip() *must* be tested *after* find_first_uip() because the former method
    //       is the one setting the IsMarked flag
    assert!(solver.is_uip(6));
}

// isUIP must be false when the literal is not false/marked
#[test]
fn is_uip_must_be_false_when_literal_is_not_false() {
    let mut solver = Solver::new(8);
    solver.add_problem_clause(vec![1]);

    // simulate clause activation
    let reason = solver.constraints[0].alias();
    assert!(solver.assign(lit(1), Some(reason)).is_ok());
    assert!(solver.propagate().is_none());

    // simulates stale data
    solver.trail.prop_queue.push(lit(1));

    assert!(!solver.is_uip(1));
}

// isUIP must be false when there is an other marked literal before next decision
#[test]
fn is_uip_must_be_false_when_there_is_an_other_marked_literal_before_next_decision(){
    /*-
     * a ------------------------------------/--- c
     *                                      /
     *     /------- e ---- f --- -b --- -h +
     *    /                    /           \
     * d /-- g ---------------/             \--- -c
     *
     */
    let mut solver = Solver::new(8);
    solver.add_problem_clause(vec![ 1,-8, 3]); // c0
    solver.add_problem_clause(vec![ 1, 4,-5]); // c1
    solver.add_problem_clause(vec![ 5,-6, 7]); // c2
    solver.add_problem_clause(vec![ 6, 2, 7]); // c3
    solver.add_problem_clause(vec![ 4,-7]);    // c4
    solver.add_problem_clause(vec![-2, 8]);    // c5
    solver.add_problem_clause(vec![-8,-3]);    // c6

    assert_eq!(Ok(()), solver.assign(lit(-1), None));
    assert_eq!(Ok(()), solver.assign(lit(-4), None));

    let conflict = solver.propagate();
    assert!(conflict.is_some());
    assert_eq!("Some(Alias(Some(Clause([Literal(3), Literal(-8), Literal(1)]))))",
               format!("{:?}", &conflict));

    assert_eq!(6, solver.find_first_uip(conflict.unwrap().get_ref().unwrap()));
    assert!(!solver.is_uip(7)); // just check that no other than the found uip is an uip
}

// findFirstUIP stops at first uip when it's not a decision (1st antecedant)
// Note: this is the same test scenario as for is_uip_must_be_true_..._before_next_decision.
//       It might be worth it to merge these two tests
#[allow(non_snake_case)]
#[test]
fn find_first_uip_stops_at_first_uip_even_if_its_not_a_decision___1st_antecedant(){
    /*-
     * a ------------------------------------/--- c
     *                                      /
     *     /------- e ---- f --- -b --- -h +
     *    /                    /           \
     * d /-- g ---------------/             \--- -c
     *
     */
    let mut solver = Solver::new(8);
    solver.add_problem_clause(vec![ 1,-8, 3]); // c0
    solver.add_problem_clause(vec![ 1, 4,-5]); // c1
    solver.add_problem_clause(vec![ 5,-6, 7]); // c2
    solver.add_problem_clause(vec![ 6, 2, 7]); // c3
    solver.add_problem_clause(vec![ 4,-7]);    // c4
    solver.add_problem_clause(vec![-2, 8]);    // c5
    solver.add_problem_clause(vec![-8,-3]);    // c6

    assert_eq!(Ok(()), solver.assign(lit(-1), None));
    assert_eq!(Ok(()), solver.assign(lit(-4), None));

    let conflict = solver.propagate();

    assert!(conflict.is_some());
    assert_eq!("Some(Alias(Some(Clause([Literal(3), Literal(-8), Literal(1)]))))", format!("{:?}", &conflict));
    assert_eq!(6, solver.find_first_uip(conflict.unwrap().get_ref().unwrap()));
    assert!(solver.is_uip(6));
}

// findFirstUIP stops at first uip when there is no uip but the decision
#[test]
fn find_first_uip_stops_at_first_uip_when_there_is_no_uip_but_the_decision(){
    /*-
     * 1 ---+---+- 3 -\
     *       \ /       \
     *        X          5
     *       / \       /
     * 2 ---+---+- 4 -/
     *
     */
    let mut solver = Solver::new(5);

    solver.add_problem_clause(vec![ 1, 2,-3]);
    solver.add_problem_clause(vec![ 1, 2,-4]);
    solver.add_problem_clause(vec![ 3, 4,-5]);
    solver.add_problem_clause(vec![ 3, 4, 5]);

    assert!(solver.assign(lit(-1), None).is_ok());
    assert!(solver.assign(lit(-2), None).is_ok());

    let conflict = solver.propagate();
    assert!(conflict.is_some());
    assert_eq!("Some(Alias(Some(Clause([Literal(-5), Literal(3), Literal(4)]))))",
               format!("{:?}", conflict));
    assert_eq!(1, solver.find_first_uip(conflict.unwrap().get_ref().unwrap()));
}


// findFirstUIP stops at first uip when it's not a decision (deeper down)
#[allow(non_snake_case)]
#[test]
fn find_first_uip_stops_at_first_uip_even_if_its_not_a_decision___deeper_down(){
    /*-
     * 1 ---+     +- 5 -\
     *       \   /       \
     *         3          6
     *       /   \       /
     * 2 ---+     +- 4 -/
     *
     */
    let mut solver = Solver::new(6);

    solver.add_problem_clause(vec![ 1, 2,-3]);
    solver.add_problem_clause(vec![ 3,-4]);
    solver.add_problem_clause(vec![ 3,-5]);
    solver.add_problem_clause(vec![ 4, 5, 6]);
    solver.add_problem_clause(vec![ 4, 5,-6]);

    assert!(solver.assign(lit(-1), None).is_ok());
    assert!(solver.assign(lit(-2), None).is_ok());

    let conflict = solver.propagate();
    assert!(conflict.is_some());
    assert_eq!("Some(Alias(Some(Clause([Literal(6), Literal(4), Literal(5)]))))",
               format!("{:?}", conflict));
    assert_eq!(2, solver.find_first_uip(conflict.unwrap().get_ref().unwrap()));
}


#[test]
fn build_conflict_clause_exemple_1st_antecedant(){
    /*-
     * a ------------------------------------/--- c
     *                                      /
     *     /------- e ---- f --- -b --- -h +
     *    /                    /           \
     * d /-- g ---------------/             \--- -c
     *
     */
    let mut solver = Solver::new(8);
    solver.add_problem_clause(vec![ 1,-8, 3]); // c0
    solver.add_problem_clause(vec![ 1, 4,-5]); // c1
    solver.add_problem_clause(vec![ 5,-6, 7]); // c2
    solver.add_problem_clause(vec![ 6, 2, 7]); // c3
    solver.add_problem_clause(vec![ 4,-7]);    // c4
    solver.add_problem_clause(vec![-2, 8]);    // c5
    solver.add_problem_clause(vec![-8,-3]);    // c6

    assert_eq!(Ok(()), solver.assign(lit(-1), None));
    assert_eq!(Ok(()), solver.assign(lit(-4), None));

    let conflict = solver.propagate();
    let uip = solver.find_first_uip(conflict.unwrap().get_ref().unwrap());
    let clause = solver.build_conflict_clause(uip);

    assert_eq!("[Literal(-8), Literal(1)]", format!("{:?}", clause));
}

#[test]
fn build_conflict_clause_exemple_no_uip_but_decision(){
    /*-
     * 1 ---+---+- 3 -\
     *       \ /       \
     *        X          5
     *       / \       /
     * 2 ---+---+- 4 -/
     *
     */
    let mut solver = Solver::new(5);

    solver.add_problem_clause(vec![ 1, 2,-3]);
    solver.add_problem_clause(vec![ 1, 2,-4]);
    solver.add_problem_clause(vec![ 3, 4,-5]);
    solver.add_problem_clause(vec![ 3, 4, 5]);

    assert!(solver.assign(lit(-1), None).is_ok());
    assert!(solver.assign(lit(-2), None).is_ok());

    let conflict = solver.propagate();
    let uip = solver.find_first_uip(conflict.unwrap().get_ref().unwrap());
    let clause = solver.build_conflict_clause(uip);

    assert_eq!("[Literal(2), Literal(1)]", format!("{:?}", clause));
}

// buildConflictClause exemple not first and not decision
#[test]
fn build_conflict_clause_exemple_not_decision_deeper_down(){
    /*-
     * 1 ---+     +- 5 -\
     *       \   /       \
     *         3          6
     *       /   \       /
     * 2 ---+     +- 4 -/
     *
     */
    let mut solver = Solver::new(6);

    solver.add_problem_clause(vec![ 1, 2,-3]);
    solver.add_problem_clause(vec![ 3,-4]);
    solver.add_problem_clause(vec![ 3,-5]);
    solver.add_problem_clause(vec![ 4, 5, 6]);
    solver.add_problem_clause(vec![ 4, 5,-6]);

    assert!(solver.assign(lit(-1), None).is_ok());
    assert!(solver.assign(lit(-2), None).is_ok());

    let conflict = solver.propagate();
    let uip = solver.find_first_uip(conflict.unwrap().get_ref().unwrap());
    let clause = solver.build_conflict_clause(uip);

    assert_eq!("[Literal(3)]", format!("{:?}", clause));
}

// buildConflictClause does omit implied literals
#[test]
fn build_conflict_clause_exemple_short_circuit(){
    /*-
     *     /---------------------\
     *    /                      \
     * 1 +--+---+- 3 -+     +-----+- 6
     *       \ /       \   /
     *        X          5
     *       / \       /   \
     * 2 +--+---+- 4 -+     +-----+ -6
     *    \                      /
     *     \--------------------/
     */
    let mut solver = Solver::new(6);

    solver.add_problem_clause(vec![ 1, 2,-3]);
    solver.add_problem_clause(vec![ 1, 2,-4]);
    solver.add_problem_clause(vec![ 3, 4,-5]);
    solver.add_problem_clause(vec![ 1, 5, 6]);
    solver.add_problem_clause(vec![ 2, 5,-6]);

    assert!(solver.assign(lit(-1), None).is_ok());
    assert!(solver.assign(lit(-2), None).is_ok());

    let conflict = solver.propagate();
    let uip = solver.find_first_uip(conflict.unwrap().get_ref().unwrap());
    let clause = solver.build_conflict_clause(uip);

    assert_eq!("[Literal(2), Literal(1)]", format!("{:?}", clause));
}

#[test]
fn build_conflict_clause_omits_implied_literals(){
    /*-
     * 1 -----------------+ 5
     *   \               /
     *    \             /
     *     \           /
     * 2 ---\------ 3 +
     *       \         \
     *        \         \
     *         \         \
     *          4 -------+ -5
     */
    let mut solver = Solver::new(5);

    solver.add_problem_clause(vec![ 1,-4]);
    solver.add_problem_clause(vec![ 2,-3]);

    solver.add_problem_clause(vec![ 3, 4, 5]);
    solver.add_problem_clause(vec![ 3, 1,-5]);

    assert!(solver.assign(lit(-1), None).is_ok());
    assert!(solver.propagate().is_none());

    assert!(solver.assign(lit(-2), None).is_ok());
    let conflict = solver.propagate();
    assert!(conflict.is_some());

    let uip = solver.find_first_uip(conflict.unwrap().get_ref().unwrap());
    assert_eq!(3, uip);

    let clause = solver.build_conflict_clause(uip);
    assert_eq!("[Literal(3), Literal(1)]", format!("{:?}", clause));
}

#[test]
fn find_backjump_point_must_rollback_everything_when_the_learned_clause_is_unit(){
    /*-
     * 1 ---+     +- 5 -\
     *       \   /       \
     *         3          6
     *       /   \       /
     * 2 ---+     +- 4 -/
     *
     */
    let mut solver = Solver::new(6);

    solver.add_problem_clause(vec![ 1, 2,-3]);
    solver.add_problem_clause(vec![ 3,-4]);
    solver.add_problem_clause(vec![ 3,-5]);
    solver.add_problem_clause(vec![ 4, 5, 6]);
    solver.add_problem_clause(vec![ 4, 5,-6]);

    assert!(solver.assign(lit(-1), None).is_ok());
    assert!(solver.assign(lit(-2), None).is_ok());

    let conflict = solver.propagate();
    let uip = solver.find_first_uip(conflict.unwrap().get_ref().unwrap());
    let clause = solver.build_conflict_clause(uip);

    assert_eq!("[Literal(3)]", format!("{:?}", clause));
    assert_eq!(0, solver.find_backjump_point(uip));
}

#[test]
fn find_backjump_point_must_go_at_least_until_the_most_recent_decision(){
    /*-
     * 1 -----------------+ 5
     *   \               /
     *    \             /
     *     \           /
     * 2 ---\------ 3 +
     *       \         \
     *        \         \
     *         \         \
     *          4 -------+ -5
     */
    let mut solver = Solver::new(5);

    solver.add_problem_clause(vec![ 1,-4]);
    solver.add_problem_clause(vec![ 2,-3]);

    solver.add_problem_clause(vec![ 3, 4, 5]);
    solver.add_problem_clause(vec![ 3, 1,-5]);

    assert!(solver.assign(lit(-1), None).is_ok());
    assert!(solver.propagate().is_none());

    assert!(solver.assign(lit(-2), None).is_ok());
    let conflict = solver.propagate();
    assert!(conflict.is_some());

    let uip = solver.find_first_uip(conflict.unwrap().get_ref().unwrap());
    assert_eq!(3, uip);

    let clause = solver.build_conflict_clause(uip);
    assert_eq!("[Literal(3), Literal(1)]", format!("{:?}", clause));
    assert_eq!(2, solver.find_backjump_point(uip));
}

#[test]
fn find_backjump_point_must_go_until_the_earliest_decision_leaving_the_learned_clause_unit(){
    /*-
     * 1 ------------------------------------------------------------+ 5
     *   \                                                          /
     *    \   6   7   8   9   10                                   /
     *     \                                                      /
     *      \                                             2 --- 3 +
     *       \                                                    \
     *        \                                                    \
     *         \                                                    \
     *          4 --------------------------------------------------+ -5
     */
    let mut solver = Solver::new(10);

    solver.add_problem_clause(vec![ 1,-4]);
    solver.add_problem_clause(vec![ 2,-3]);

    solver.add_problem_clause(vec![ 3, 4, 5]);
    solver.add_problem_clause(vec![ 3, 1,-5]);

    // 1
    assert!(solver.assign(lit(-1), None).is_ok());
    assert!(solver.propagate().is_none());
    // 6
    assert!(solver.assign(lit(-6), None).is_ok());
    assert!(solver.propagate().is_none());
    // 7
    assert!(solver.assign(lit(-7), None).is_ok());
    assert!(solver.propagate().is_none());
    // 8
    assert!(solver.assign(lit(-8), None).is_ok());
    assert!(solver.propagate().is_none());
    // 9
    assert!(solver.assign(lit(-9), None).is_ok());
    assert!(solver.propagate().is_none());
    // 10
    assert!(solver.assign(lit(-10), None).is_ok());
    assert!(solver.propagate().is_none());

    assert!(solver.assign(lit(-2), None).is_ok());
    let conflict = solver.propagate();
    assert!(conflict.is_some());

    let uip = solver.find_first_uip(conflict.unwrap().get_ref().unwrap());
    assert_eq!(8, uip);

    let clause = solver.build_conflict_clause(uip);
    assert_eq!("[Literal(3), Literal(1)]", format!("{:?}", clause));
    assert_eq!(2, solver.find_backjump_point(uip));
}

#[test]
// rollback undoes all the choices (propagated or not) until the given limit
fn rollback_undoes_all_choices_until_the_limit() {
    let mut solver = Solver::new(5);

    for i in 1..6 {
        assert!(solver.assign(lit(i), None).is_ok());
        solver.nb_decisions += 1; // technically, this should be a call to .decide()
    }

    solver.rollback(0);

    assert!(solver.valuation.is_undef(lit(1)));
    assert!(solver.valuation.is_undef(lit(2)));
    assert!(solver.valuation.is_undef(lit(3)));
    assert!(solver.valuation.is_undef(lit(4)));
    assert!(solver.valuation.is_undef(lit(5)));
}

#[test]
// rollback drops the analysis markers on all the elements between the root
// level (included) and the given limit.
//
// -> No decision is undone but the analysis is reset
fn rollback_drops_all_flags_from_the_given_limit_until_the_root(){
    let mut solver = Solver::new(5);

    for i in 1..6 {
        let lit = lit(i);
        assert!(solver.assign(lit, None).is_ok());
        solver.nb_decisions += 1; // technically, this should be a call to .decide()

        // TODO turn these to dedicated methods
        solver.flags[-lit].set(Flag::IsMarked);
        solver.flags[-lit].set(Flag::IsImplied);
        solver.flags[-lit].set(Flag::IsNotImplied);
        solver.flags[-lit].set(Flag::IsInConflictClause);

    }

    assert_eq!(5, solver.nb_decisions);

    solver.rollback(5);

    // it changed nothing
    assert_eq!(5, solver.nb_decisions);
    for i in 1..6 {
        let l = lit(i);
        assert!(solver.valuation.is_true(l));
        assert!(!solver.flags[l].is_set(Flag::IsMarked));
        assert!(!solver.flags[l].is_set(Flag::IsImplied));
        assert!(!solver.flags[l].is_set(Flag::IsNotImplied));
        assert!(!solver.flags[l].is_set(Flag::IsInConflictClause));

        assert!(solver.valuation.is_false(-l));
        assert!(!solver.flags[-l].is_set(Flag::IsMarked));
        assert!(!solver.flags[-l].is_set(Flag::IsImplied));
        assert!(!solver.flags[-l].is_set(Flag::IsNotImplied));
        assert!(!solver.flags[-l].is_set(Flag::IsInConflictClause));
    }
}

#[test]
// rollback drops the analysis markers on all the elements between the root
// level (included) and the given limit
fn rollback_undoes_and_clears_analysis() {
    let mut solver = Solver::new(5);

    for i in 1..6 {
        let lit = lit(i);
        assert!(solver.assign(lit, None).is_ok());
        solver.nb_decisions += 1; // technically, this should be a call to .decide()

        // TODO turn these to dedicated methods
        solver.flags[-lit].set(Flag::IsMarked);
        solver.flags[-lit].set(Flag::IsImplied);
        solver.flags[-lit].set(Flag::IsNotImplied);
        solver.flags[-lit].set(Flag::IsInConflictClause);
    }

    assert_eq!(5, solver.nb_decisions);
    solver.rollback(3);
    assert_eq!(3, solver.nb_decisions);
}