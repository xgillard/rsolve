use std::clone::Clone;
use std::ops::*;

use utils::*;
use core::*;
use flags::*;
use collections::*;
use branching::*;

type Watcher = Alias<Clause>;
type Conflict= Alias<Clause>;
type Reason  = Alias<Clause>;

// -----------------------------------------------------------------------------------------------
/// # Conflict
/// A simple algebraic type to explicit the fact that some clause is conflicting
// -----------------------------------------------------------------------------------------------
#[derive(Debug)]
pub struct Solver {
    pub trail       : Trail,
    pub constraints : Vec<Aliasable<Clause>>,
    pub learned     : Vec<Aliasable<Clause>>,

    /// Watchers: vectors of watchers associated with each literal.
    /// _Important Notice_ : A clause should watch a literal it owns, not its negation !
    pub watchers    : LitIdxVec<Vec<Watcher>>,
    /// The flags associated with each literal
    pub flags       : LitIdxVec<Flags>,
    /// The variable ordering heuristic (derivative of vsids)
    pub var_order   : VariableOrdering,

    /// The number of conflicts that have occurred since the last restart
    pub nb_conflicts: uint,
    /// The number of restarts that have occured since the very beginning
    pub nb_restarts : usize
}

impl Solver {
    pub fn new(nb_vars: usize) -> Solver {
        let mut solver = Solver {
            trail : Trail {
                forced    : 0,
                propagated: 0,
                prop_queue: Vec::with_capacity(nb_vars),
                valuation : Valuation::new(nb_vars)
            },

            constraints : vec![],
            learned     : vec![],

            watchers    : LitIdxVec::with_capacity(nb_vars),
            flags       : LitIdxVec::with_capacity(nb_vars),
            var_order   : VariableOrdering::new(nb_vars as uint),

            nb_conflicts: 0,
            nb_restarts : 0
        };

        // initialize empty watchers lists
        for _ in 0..nb_vars {
            solver.watchers.push_values(vec![], vec![]);
            solver.flags   .push_values(Flags::new(), Flags::new());
        }

        return solver;
    }

    pub fn add_problem_clause(&mut self, c :Vec<iint>) {
        let watched: Vec<Literal> = c.iter()
                                     .take(2)
                                     .map(|l|Literal::from(*l))
                                     .collect();

        let clause = Aliasable::new(Clause::from(c));

        self.constraints.push( clause);

        for l in watched {
            self.watchers[l].push(self.constraints.last().unwrap().alias());
        }
    }
    pub fn add_learned_clause(&mut self, c :Vec<iint>) {
        let watched: Vec<Literal> = c.iter()
            .take(2)
            .map(|l|Literal::from(*l))
            .collect();

        let clause = Aliasable::new(Clause::from(c));

        self.learned.push( clause);

        for l in watched {
            self.watchers[l].push(self.learned.last().unwrap().alias());
        }
    }

    // -------------------------------------------------------------------------------------------//
    // ---------------------------- PROPAGATION --------------------------------------------------//
    // -------------------------------------------------------------------------------------------//

	/// This method propagates the information about all the literals that have been
	/// enqueued. It returns an optional conflicting clause whenever conflict is detected
	/// Otherwise, None is returned.
    pub fn propagate(&mut self) -> Option<Conflict> {
        loop {
            if self.trail.propagated >= self.trail.prop_queue.len() { break }

            let nb_propagated = self.trail.propagated;
            let literal = self.trail.prop_queue[nb_propagated];

            let conflict = self.propagate_literal(literal);
            if conflict.is_some() {
                return conflict;
            }

            self.trail.propagated += 1;
        }
        return None;
    }

	/// Notifies all the watchers of `lit` that `lit` has been falsified.
	/// This method optionally returns a conflicting clause if one is found.
    pub fn propagate_literal(&mut self, lit : Literal) -> Option<Conflict> {
        // we loop backwards to avoid messing up with the items that are appended to the list while
        // iterating over it. Logically, the two sets should be separated (but merged after the fn).
        // This iterating scheme achieves that goal.
        for i in (0..self.watchers[lit].len()).rev() {
            let watcher = self.watchers[lit][i].clone();
            self.watchers[lit].swap_remove(i);

            match watcher.get_mut() {
                None         => { /* The clause was deteted, hence the watcher can be ignored */ },
                Some(clause) => {
                    match clause.find_new_literal(lit, &self.trail.valuation) {
                        Ok (l) => {
                            // l was found, its ok. We only need to start watching it
                            self.watchers[l].push(watcher.clone());
                        },
                        Err(l) => {
                            // No result could be found, so we need to keep watching `lit`
                            self.watchers[lit].push(watcher.clone());
                            // In the meantime we also need to assign `l`, otherwise the whole
                            // clause is going to be unsat
                            match self.trail.assign(l, Some(watcher.clone())) {
                                // Assignment went on well, we're done
                                Ok(()) => { },
                                // Conflict detected, return it !
                                Err(())=> return Some(watcher.clone())
                            }
                        }
                    }
                }
            }
        }

        return None;
    }

    // -------------------------------------------------------------------------------------------//
    // ---------------------------- CLAUSE LEARNING ----------------------------------------------//
    // -------------------------------------------------------------------------------------------//

	/// This method builds a and returns minimized conflict clause by walking the marked literals
    /// to compute a cut.
    ///
	/// `uip` is the position of the 1st uip
    pub fn build_conflict_clause(&mut self, uip: usize) -> Clause {
        let mut learned = Vec::new();

        for cusor in (self.trail.forced..uip+1).rev() {
            let lit = self.trail.prop_queue[cusor];

            if self.is_marked(lit) && !self.is_implied(lit) {
                learned.push(lit);
                self.flags[lit].set(Flag::IsInConflictClause);
            }
        }

        return Clause::new(learned);
    }

	/// Finds the position (in `prop_queue`) of the first unique implication point
	/// implying the conflict detected because of `conflicting`. Concretely, this
	/// is implemented with a backwards BFS traversal of the implication graph and
	/// each step is an inverse resolution.
	///
	/// `conflicting` is the clause which was detected to be the reason of the conflict
	/// This function returns the position of the first uip
    pub fn find_first_uip(&mut self, conflicting: &Clause) -> usize {
        // mark all literals in the conflict clause
        for l in conflicting.iter() {
            self.mark_and_bump(*l);
        }

        // backwards BFS rooted at the conflict to identify uip (and mark its cause)
        let mut cursor = self.trail.prop_queue.len();
        loop {
            cursor -= 1;

            // Whenever we've analyzed all the literals that are not *forced* by the constraints,
            // we can stop.
            if cursor < self.trail.forced { break }

            // Whenever we've found an UIP, it is bound to be the first one. Hence, we can stop
            if self.is_uip(cursor){ break }

            // otherwise, we just proceed with the rest
            let lit = self.trail.prop_queue[cursor];

            // if a literal is not marked, we don't need to care about it
            if !self.is_marked(lit) { continue }

            // otherwise, we need to mark all the literal in its antecedent. Note, we know lit is no
            // decision literal because, if it were, the is_uip() would have been true.
            match self.trail.valuation.get_reason(lit) {
                // will never happen
                None => panic!("{:?} is a decision (it has no reason), but is_uip() replied false"),
                Some(alias) => match alias.get_ref() {
                    // will not happen either
                    None => panic!("The reason of {:?} was deleted but I still need it !"),
                    // will always happen
                    Some(cause) => {
                        for l in cause.iter().skip(1) {
                            self.mark_and_bump(*l);
                        }
                    }
                }
            }
        }

        return cursor;
    }

    /// Returns the position (index in `prop_queue`) until which the solver should backtrack
    /// to continue searching while incorporating the knowledge gained with learned clause
    /// implying `uip`.
    ///
    /// The returned position corresponds to the index of the *earliest* decision point which
    /// makes the learned clause unit.
    pub fn find_backjump_point(&self, uip: usize) -> usize {
        let mut count_used    = 0;
        let mut backjump = uip;

        for cursor in (self.trail.forced..uip+1).rev() {
            let lit = self.trail.prop_queue[cursor];

            if self.flags[lit].is_set(Flag::IsInConflictClause) {
                count_used += 1;
            }

            if count_used == 1 && self.trail.is_decision(lit) {
                backjump = cursor;
            }
        }

        return backjump;
    }

    /// Returns true iff the given `position` (index) in the trail `prop_queue` is an unique
    /// implication point (UIP). A position is an uip if:
    /// - it is a decision.
    /// - it is the last marked literal before a decision.
    pub fn is_uip(&self, position: usize) -> bool {
        let literal = self.trail.prop_queue[position];

        if self.trail.is_decision(literal) {
            return true;
        }

        if !self.is_marked(literal) {
            return false;
        }

        for iter in (self.trail.forced..position).rev() {
            let iter_literal= self.trail.prop_queue[iter];

            if self.is_marked(iter_literal) {
                return false;
            }
            if self.trail.is_decision(iter_literal) {
                return true;
            }
        }

        return false;
    }

    /// Convenience (private) method to mark and bump a literal during conflict analysis iff it has
    /// not been marked-bumped yet
    fn mark_and_bump(&mut self, lit : Literal) {
        if !self.is_marked(lit) {
            self.mark(lit);
            self.var_order.bump(lit.var(), self.nb_conflicts);
        }
    }


    fn is_marked(&self, lit : Literal) -> bool {
        self.flags[lit].is_set(Flag::IsMarked)
    }
    fn mark(&mut self, lit : Literal) {
        self.flags[lit].set(Flag::IsMarked)
    }
    /// returns true iff recursive analysis showed `lit` to be implied by other literals
    fn is_implied(&mut self, lit: Literal) -> bool {
        // If it's already been analyzed, reuse that info
        let flags_lit = self.flags[lit];
        if flags_lit.one_of(Flag::IsImplied, Flag::IsNotImplied) {
            return flags_lit.is_set(Flag::IsImplied);
        }

        match self.trail.valuation.get_reason(lit) {
            // If it's a decision, there's no way it is implied
            None        => return false,
            Some(alias) => match alias.get_ref() {
                // will not happen either
                None => panic!("The reason of {:?} was deleted but I still need it !"),
                // will always happen
                Some(cause) => {
                    for l in cause.iter().skip(1) {
                        if !self.is_marked(*l) && !self.is_implied(*l) {
                            self.flags[lit].set(Flag::IsNotImplied);
                            return false;
                        }
                    }
                    self.flags[lit].set(Flag::IsImplied);
                    return true;
                }
            }
        }
    }
}

// -----------------------------------------------------------------------------------------------
/// # Valuation
/// This struct encapsulates the idea of an assignment of Variables to Bool values.
// -----------------------------------------------------------------------------------------------

#[derive(Debug)]
pub struct VariableState {
    pub value : Bool,
    pub reason: Option<Reason>
}

impl VariableState {
    pub fn default() -> VariableState {
        VariableState{value: Bool::Undef, reason: None}
    }
}

#[derive(Debug)]
pub struct Valuation ( VarIdxVec<VariableState> );

impl Valuation {

    pub fn new(nb_vars: usize) -> Valuation {
        let mut valuation= Valuation(VarIdxVec::with_capacity(nb_vars));
        // initialize the items
        for _ in 0..nb_vars {
            valuation.0.push(VariableState::default() );
        }
        return valuation;
    }

    pub fn get_value(&self, l: Literal) -> Bool {
        let value = self.0[l.var()].value;

        match l.sign() {
            Sign::Positive =>  value,
            Sign::Negative => !value
        }
    }

    pub fn get_reason(&self, l : Literal) -> Option<Reason> {
        self.0[l.var()].reason.clone()
    }

    pub fn set_value(&mut self, l: Literal, value : Bool, reason: Option<Reason>) {
        self.0[l.var()] = match l.sign() {
            Sign::Positive => VariableState{value:  value, reason},
            Sign::Negative => VariableState{value: !value, reason}
        }
    }

    pub fn is_undef(&self, l: Literal) -> bool {
        self.0[l.var()].value == Bool::Undef
    }
    pub fn is_true (&self, l: Literal) -> bool {
        match l.sign() {
            Sign::Positive => self.0[l.var()].value == Bool::True,
            Sign::Negative => self.0[l.var()].value == Bool::False,
        }
    }
    pub fn is_false(&self, l: Literal) -> bool {
        match l.sign() {
            Sign::Positive => self.0[l.var()].value == Bool::False,
            Sign::Negative => self.0[l.var()].value == Bool::True,
        }
    }
}

impl Deref for Valuation {
    type Target = VarIdxVec<VariableState>;

    #[inline]
    fn deref(&self) -> &VarIdxVec<VariableState> {
        &self.0
    }
}

impl DerefMut for Valuation {
    #[inline]
    fn deref_mut(&mut self) -> &mut VarIdxVec<VariableState> {
        &mut self.0
    }
}

// -----------------------------------------------------------------------------------------------
/// # Trail
/// The structure that memorizes the state and order in which literals have been assigned
// -----------------------------------------------------------------------------------------------
#[derive(Debug)]
pub struct Trail {
    pub valuation  : Valuation,
    pub prop_queue : Vec<Literal>,
    pub forced     : usize,
    pub propagated : usize
}

impl Trail {
    /// Assigns a given literal to True. That is to say, it assigns a value to the given literal
    /// in the Valuation and it enqueues the negation of the literal on the propagation queue
    ///
    /// # Note
    /// We always push the *negation* of the assigned literal on the stack
    pub fn assign(&mut self, lit: Literal, reason: Option<Reason>) -> Result<(), ()> {
        match self.valuation.get_value(lit) {
            Bool::True  => Ok(()),
            Bool::False => Err(()),
            Bool::Undef => {
                self.valuation.set_value(lit, Bool::True, reason);
                self.prop_queue.push(!lit);
                Ok(())
            }
        }
    }

    pub fn is_decision(&self, lit : Literal) -> bool {
        self.valuation[lit.var()].reason.is_none()
    }
}

#[cfg(test)]
mod test_solver {
    use super::*;
    use super::super::*;

    #[test]
    fn propagate_processes_everything_until_a_fixed_point_is_reached(){
        let mut solver = Solver::new(3);

        // initialize the constraint database
        solver.add_problem_clause(vec![1, -2, -3]);
        solver.add_problem_clause(vec![2, -3]);
        solver.add_problem_clause(vec![3]);

        // start the test (for real !)
        solver.trail.assign(Literal::from(3), None).expect("3 should be assignable");

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
        solver.trail.assign(Literal::from( 3), None).expect(" 3 should be assignable");
        // if I propagated here, then -2 shouldn't be assignable anymore
        solver.trail.assign(Literal::from(-2), None).expect("-2 should be assignable");

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

        assert_eq!(Ok(()), solver.trail.assign(lit(-1), None));
        assert_eq!(Ok(()), solver.trail.assign(lit(-4), None));

        let conflict = solver.propagate();
        assert!(conflict.is_some());
        assert_eq!(format!("{:?}", solver.constraints[0].alias()),
                   format!("{:?}", conflict.unwrap()));
    }

    // isUIP must be true when the literal is a decision
    #[test]
    fn is_uip_must_be_true_when_literal_is_a_decision() {
        let mut solver = Solver::new(8);

        solver.trail.assign(lit(2), None).expect("2 must be assignable");
        solver.trail.assign(lit(4), None).expect("4 must be assignable");
        solver.trail.assign(lit(8), None).expect("8 must be assignable");

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

        assert_eq!(Ok(()), solver.trail.assign(lit(-1), None));
        assert_eq!(Ok(()), solver.trail.assign(lit(-4), None));

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
        assert!(solver.trail.assign(lit(1), Some(solver.constraints[0].alias())).is_ok());
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

        assert_eq!(Ok(()), solver.trail.assign(lit(-1), None));
        assert_eq!(Ok(()), solver.trail.assign(lit(-4), None));

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

        assert_eq!(Ok(()), solver.trail.assign(lit(-1), None));
        assert_eq!(Ok(()), solver.trail.assign(lit(-4), None));

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

        assert!(solver.trail.assign(lit(-1), None).is_ok());
        assert!(solver.trail.assign(lit(-2), None).is_ok());

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

        assert!(solver.trail.assign(lit(-1), None).is_ok());
        assert!(solver.trail.assign(lit(-2), None).is_ok());

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

        assert_eq!(Ok(()), solver.trail.assign(lit(-1), None));
        assert_eq!(Ok(()), solver.trail.assign(lit(-4), None));

        let conflict = solver.propagate();
        let uip = solver.find_first_uip(conflict.unwrap().get_ref().unwrap());
        let clause = solver.build_conflict_clause(uip);

        assert_eq!("Clause([Literal(-8), Literal(1)])", format!("{:?}", clause));
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

        assert!(solver.trail.assign(lit(-1), None).is_ok());
        assert!(solver.trail.assign(lit(-2), None).is_ok());

        let conflict = solver.propagate();
        let uip = solver.find_first_uip(conflict.unwrap().get_ref().unwrap());
        let clause = solver.build_conflict_clause(uip);

        assert_eq!("Clause([Literal(2), Literal(1)])", format!("{:?}", clause));
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

        assert!(solver.trail.assign(lit(-1), None).is_ok());
        assert!(solver.trail.assign(lit(-2), None).is_ok());

        let conflict = solver.propagate();
        let uip = solver.find_first_uip(conflict.unwrap().get_ref().unwrap());
        let clause = solver.build_conflict_clause(uip);

        assert_eq!("Clause([Literal(3)])", format!("{:?}", clause));
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

        assert!(solver.trail.assign(lit(-1), None).is_ok());
        assert!(solver.trail.assign(lit(-2), None).is_ok());

        let conflict = solver.propagate();
        let uip = solver.find_first_uip(conflict.unwrap().get_ref().unwrap());
        let clause = solver.build_conflict_clause(uip);

        assert_eq!("Clause([Literal(2), Literal(1)])", format!("{:?}", clause));
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

        assert!(solver.trail.assign(lit(-1), None).is_ok());
        assert!(solver.propagate().is_none());

        assert!(solver.trail.assign(lit(-2), None).is_ok());
        let conflict = solver.propagate();
        assert!(conflict.is_some());

        let uip = solver.find_first_uip(conflict.unwrap().get_ref().unwrap());
        assert_eq!(3, uip);

        let clause = solver.build_conflict_clause(uip);
        assert_eq!("Clause([Literal(3), Literal(1)])", format!("{:?}", clause));
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

        assert!(solver.trail.assign(lit(-1), None).is_ok());
        assert!(solver.trail.assign(lit(-2), None).is_ok());

        let conflict = solver.propagate();
        let uip = solver.find_first_uip(conflict.unwrap().get_ref().unwrap());
        let clause = solver.build_conflict_clause(uip);

        assert_eq!("Clause([Literal(3)])", format!("{:?}", clause));
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

        assert!(solver.trail.assign(lit(-1), None).is_ok());
        assert!(solver.propagate().is_none());

        assert!(solver.trail.assign(lit(-2), None).is_ok());
        let conflict = solver.propagate();
        assert!(conflict.is_some());

        let uip = solver.find_first_uip(conflict.unwrap().get_ref().unwrap());
        assert_eq!(3, uip);

        let clause = solver.build_conflict_clause(uip);
        assert_eq!("Clause([Literal(3), Literal(1)])", format!("{:?}", clause));
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
        assert!(solver.trail.assign(lit(-1), None).is_ok());
        assert!(solver.propagate().is_none());
        // 6
        assert!(solver.trail.assign(lit(-6), None).is_ok());
        assert!(solver.propagate().is_none());
        // 7
        assert!(solver.trail.assign(lit(-7), None).is_ok());
        assert!(solver.propagate().is_none());
        // 8
        assert!(solver.trail.assign(lit(-8), None).is_ok());
        assert!(solver.propagate().is_none());
        // 9
        assert!(solver.trail.assign(lit(-9), None).is_ok());
        assert!(solver.propagate().is_none());
        // 10
        assert!(solver.trail.assign(lit(-10), None).is_ok());
        assert!(solver.propagate().is_none());

        assert!(solver.trail.assign(lit(-2), None).is_ok());
        let conflict = solver.propagate();
        assert!(conflict.is_some());

        let uip = solver.find_first_uip(conflict.unwrap().get_ref().unwrap());
        assert_eq!(8, uip);

        let clause = solver.build_conflict_clause(uip);
        assert_eq!("Clause([Literal(3), Literal(1)])", format!("{:?}", clause));
        assert_eq!(2, solver.find_backjump_point(uip));
    }
}