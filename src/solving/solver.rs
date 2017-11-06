// TODO: Pour rejoindre jsat, il faut encore restarter, supprimer, solve et parser
use std::clone::Clone;

use utils::*;
use core::*;
use collections::*;
use solving::*;

type Watcher = Alias<Clause>;
type Conflict= Alias<Clause>;
type Reason  = Alias<Clause>;

// -----------------------------------------------------------------------------------------------
/// # Solver
/// This structure encapsulates the state of the solver. The associated methods define the CDCL
/// solving behavior.
// -----------------------------------------------------------------------------------------------
#[derive(Debug)]
pub struct Solver {
    // ~~~ # Statistics ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    /// The number of decisions that have been taken (so far) during the search
    nb_decisions : uint,
    /// The number of conflicts that have occurred since the last restart
    nb_conflicts : uint,
    /// The number of restarts that have occured since the very beginning
    nb_restarts  : usize,

    // ~~~ # Solver State ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    /// The current assignment of boolean values to variables
    valuation    : Valuation,
    /// The constraints that are forced by the problem definition
    constraints  : Vec<Aliasable<Clause>>,

    // ~~~ # Heuristics ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    /// The variable ordering heuristic (derivative of vsids)
    var_order    : VariableOrdering,
    /// The partial valuation remembering the last phase of each variable
    phase_saving : Valuation,
    /// The restart strategt (luby)
    restart_strat: LubyRestartStrategy,

    // ~~~ # Propagation ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    /// Watchers: vectors of watchers associated with each literal.
    /// _Important Notice_ : A clause should watch a literal it owns, not its negation !
    watchers     : LitIdxVec<Vec<Watcher>>,
    /// The trail of decisions and propagations that have been made so far
    prop_queue   : Vec<Literal>,
    /// The index up to which all assignments are _forced_. That is to say, these literals are
    /// directly follow from the problem definition.
    ///
    /// Note: `forced == i` means that all literals in `prop_queue` at an index _strictly_ smaller
    ///       than `i` are consequence of the definition. `prop_queue[forced]` is *not* itself a
    ///       consequence.
    forced       : usize,
    /// The index up to which all assignments have been propagated.
    ///
    /// Note: `propagated == i` means that all literals in `prop_queue` at an index _strictly_
    ///       smaller than `i` have been propagated. `prop_queue[propagated]` denotes the next
    ///       assignment to propagate
    propagated   : usize,

    // ~~~ # Clause Learning ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    /// The database of learned clauses
    learned      : Vec<Aliasable<Clause>>,
    /// The reason associated with each assignment
    reason       : VarIdxVec<Option<Reason>>,
    /// The flags used during conflict analysis. One set of flag is associated with each literal.
    flags        : LitIdxVec<Flags>
}

impl Solver {
    pub fn new(nb_vars: usize) -> Solver {
        let mut solver = Solver {
            nb_decisions : 0,
            nb_restarts  : 0,
            nb_conflicts : 0,

            valuation    : Valuation::new(nb_vars),
            constraints  : vec![],

            var_order    : VariableOrdering::new(nb_vars as uint),
            phase_saving : Valuation::new(nb_vars),
            restart_strat: LubyRestartStrategy::new(6),

            watchers     : LitIdxVec::with_capacity(nb_vars),
            prop_queue   : Vec::with_capacity(nb_vars),
            forced       : 0,
            propagated   : 0,

            learned      : vec![],
            reason       : VarIdxVec::with_capacity(nb_vars),
            flags        : LitIdxVec::with_capacity(nb_vars)
        };

        // initialize vectors
        for _ in 0..nb_vars {
            solver.watchers.push_values(vec![], vec![]);
            solver.flags   .push_values(Flags::new(), Flags::new());
            solver.reason  .push(None);
        }

        return solver;
    }

    // TODO: rename post constraint ?
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

    fn add_learned_clause(&mut self, c :Vec<Literal>) {
        let watched: Vec<Literal> = c.iter()
            .take(2)
            .map(|l| *l)
            .collect();

        let clause = Aliasable::new(Clause::from(c));

        self.learned.push( clause);

        for l in watched {
            self.watchers[l].push(self.learned.last().unwrap().alias());
        }
    }

    // -------------------------------------------------------------------------------------------//
    // ---------------------------- SEARCH -------------------------------------------------------//
    // -------------------------------------------------------------------------------------------//

    /// Returns the next literal to branch on. This method uses the variable ordering
    /// heuristic (based on vsids) and the phase saving mechanism built-in the variables.
    /// Whenever all variables have been assigned, this method returns None in order to mean
    /// that no literal is available for branching.
    fn decide(&mut self) -> Option<Literal> {

        while !self.var_order.is_empty() {
            let variable = self.var_order.pop_top();
            let positive = Literal::from_var(variable, Sign::Positive);

            if self.valuation.is_undef(positive) {
                let saved = self.phase_saving.get_value(positive);
                return match saved {
                    Bool::True  => return Some(positive),
                    Bool::False => return Some(!positive),
                    Bool::Undef => return Some(!positive)
                }
            }
        }

        return None;
    }

    // -------------------------------------------------------------------------------------------//
    // ---------------------------- PROPAGATION --------------------------------------------------//
    // -------------------------------------------------------------------------------------------//

    /// Assigns a given literal to True. That is to say, it assigns a value to the given literal
    /// in the Valuation and it enqueues the negation of the literal on the propagation queue
    ///
    /// # Note
    /// We always push the *negation* of the assigned literal on the stack
    fn assign(&mut self, lit: Literal, reason: Option<Reason>) -> Result<(), ()> {
        match self.valuation.get_value(lit) {
            Bool::True  => Ok(()),
            Bool::False => Err(()),
            Bool::Undef => {
                // if its a decision, make sure to take that into account
                if reason.is_none() {
                    self.nb_decisions += 1;
                }

                // if the solver is at root level, then assignment must follow from the problem
                if self.nb_decisions == 0 {
                    self.forced += 1;
                }

                self.valuation.set_value(lit, Bool::True);
                self.reason[lit.var()] = reason;
                self.prop_queue.push(!lit);
                Ok(())
            }
        }
    }

	/// This method propagates the information about all the literals that have been
	/// enqueued. It returns an optional conflicting clause whenever conflict is detected
	/// Otherwise, None is returned.
    fn propagate(&mut self) -> Option<Conflict> {
        loop {
            if self.propagated >= self.prop_queue.len() { break }

            let nb_propagated = self.propagated;
            let literal = self.prop_queue[nb_propagated];

            let conflict = self.propagate_literal(literal);
            if conflict.is_some() {
                return conflict;
            }

            self.propagated += 1;
        }
        return None;
    }

	/// Notifies all the watchers of `lit` that `lit` has been falsified.
	/// This method optionally returns a conflicting clause if one is found.
    fn propagate_literal(&mut self, lit : Literal) -> Option<Conflict> {
        // we loop backwards to avoid messing up with the items that are appended to the list while
        // iterating over it. Logically, the two sets should be separated (but merged after the fn).
        // This iterating scheme achieves that goal.
        for i in (0..self.watchers[lit].len()).rev() {
            let watcher = self.watchers[lit][i].clone();
            self.watchers[lit].swap_remove(i);

            match watcher.get_mut() {
                None         => { /* The clause was deteted, hence the watcher can be ignored */ },
                Some(clause) => {
                    match clause.find_new_literal(lit, &self.valuation) {
                        Ok (l) => {
                            // l was found, its ok. We only need to start watching it
                            self.watchers[l].push(watcher.clone());
                        },
                        Err(l) => {
                            // No result could be found, so we need to keep watching `lit`
                            self.watchers[lit].push(watcher.clone());
                            // In the meantime we also need to assign `l`, otherwise the whole
                            // clause is going to be unsat
                            match self.assign(l, Some(watcher.clone())) {
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
    // ---------------------------- CONFLICT RESOLUTION ------------------------------------------//
    // -------------------------------------------------------------------------------------------//

    /// This method analyzes the conflict to derive a new clause, add it to the database and
    /// rolls back the assignment stack until the moment where the solver has reached a stable
    /// and useful state (from which progress can be made).
    ///
    /// # Return Value
    /// Ok  whenever the conflict could safely be resolved,
    /// Err when the conflict could not be resolved (that is to say, when the problem is
    ///     proven to be UNSAT
    fn resolve_conflict(&mut self, conflicting: &Clause) -> Result<(), ()> {
        let uip = self.find_first_uip(conflicting);
        let learned = self.build_conflict_clause(uip);
        let backjump = self.find_backjump_point(uip);

        self.rollback(backjump);

        self.add_learned_clause(learned);

        let alias = self.learned.last().unwrap().alias();
        let learned = alias.get_ref().unwrap();
        let asserting_lit = learned[0];
        return self.assign(asserting_lit, Some(alias.clone()));
    }

	/// This method builds a and returns minimized conflict clause by walking the marked literals
    /// to compute a cut.
    ///
	/// `uip` is the position of the 1st uip
    fn build_conflict_clause(&mut self, uip: usize) -> Vec<Literal> {
        let mut learned = Vec::new();

        for cusor in (self.forced..uip+1).rev() {
            let lit = self.prop_queue[cusor];

            if self.flags[lit].is_set(Flag::IsMarked) && !Solver::is_implied(lit, &mut self.flags, &self.reason) {
                learned.push(lit);
                self.flags[lit].set(Flag::IsInConflictClause);
            }
        }

        return learned;
    }

	/// Finds the position (in `prop_queue`) of the first unique implication point
	/// implying the conflict detected because of `conflicting`. Concretely, this
	/// is implemented with a backwards BFS traversal of the implication graph and
	/// each step is an inverse resolution.
	///
	/// `conflicting` is the clause which was detected to be the reason of the conflict
	/// This function returns the position of the first uip
    fn find_first_uip(&mut self, conflicting: &Clause) -> usize {
        // mark all literals in the conflict clause
        for l in conflicting.iter() {
            Solver::mark_and_bump(*l, self.nb_conflicts, &mut self.flags, &mut self.var_order);
        }

        // backwards BFS rooted at the conflict to identify uip (and mark its cause)
        let mut cursor = self.prop_queue.len();
        loop {
            cursor -= 1;

            // Whenever we've analyzed all the literals that are not *forced* by the constraints,
            // we can stop.
            if cursor < self.forced { break }

            // Whenever we've found an UIP, it is bound to be the first one. Hence, we can stop
            if self.is_uip(cursor){ break }

            // otherwise, we just proceed with the rest
            let lit = self.prop_queue[cursor];

            // if a literal is not marked, we don't need to care about it
            if !self.flags[lit].is_set(Flag::IsMarked) { continue }

            // otherwise, we need to mark all the literal in its antecedent. Note, we know lit is no
            // decision literal because, if it were, the is_uip() would have been true.
            match &self.reason[lit.var()] {
                // will never happen
                &None => panic!("{:?} is a decision (it has no reason), but is_uip() replied false"),
                &Some(ref alias) => match alias.get_ref() {
                    // will not happen either
                    None => panic!("The reason of {:?} was deleted but I still need it !"),
                    // will always happen
                    Some(cause) => {
                        for l in cause.iter().skip(1) {
                            Solver::mark_and_bump(*l, self.nb_conflicts, &mut self.flags, &mut self.var_order);
                        }
                    }
                }
            }
        }

        return cursor;
    }

    /// Returns true iff the given `position` (index) in the trail `prop_queue` is an unique
    /// implication point (UIP). A position is an uip if:
    /// - it is a decision.
    /// - it is the last marked literal before a decision.
    fn is_uip(&self, position: usize) -> bool {
        let literal = self.prop_queue[position];

        if self.is_decision(literal) {
            return true;
        }

        if !self.flags[literal].is_set(Flag::IsMarked) {
            return false;
        }

        for iter in (self.forced..position).rev() {
            let iter_literal= self.prop_queue[iter];

            if self.flags[iter_literal].is_set(Flag::IsMarked) {
                return false;
            }
            if self.is_decision(iter_literal) {
                return true;
            }
        }

        return false;
    }

    /// Returns true iff recursive analysis showed `lit` to be implied by other literals
    ///
    /// # Note
    /// This function is implemented as an associated function in order to get over the complaints
    /// of the borrow checker. Indeed, this fn is used in contexts where &self is already borrowed
    /// mutably/immutably. This function solves the problem by explicily mentioning which parts of
    /// the state are required to be muted.
    ///
    fn is_implied(lit: Literal, flags: &mut LitIdxVec<Flags>, reason: &VarIdxVec<Option<Reason>>) -> bool {
        // If it's already been analyzed, reuse that info
        let flags_lit = flags[lit];
        if flags_lit.one_of(Flag::IsImplied, Flag::IsNotImplied) {
            return flags_lit.is_set(Flag::IsImplied);
        }

        match &reason[lit.var()] {
            // If it's a decision, there's no way it is implied
            &None            => return false,
            &Some(ref alias) => match alias.get_ref() {
                // will not happen either
                None => panic!("The reason of {:?} was deleted but I still need it !"),
                // will always happen
                Some(cause) => {
                    for l in cause.iter().skip(1) {
                        if !flags[*l].is_set(Flag::IsMarked) && !Solver::is_implied(*l, flags, reason) {
                            flags[lit].set(Flag::IsNotImplied);
                            return false;
                        }
                    }
                    flags[lit].set(Flag::IsImplied);
                    return true;
                }
            }
        }
    }

    /// Returns the position (index in `prop_queue`) until which the solver should backtrack
    /// to continue searching while incorporating the knowledge gained with learned clause
    /// implying `uip`.
    ///
    /// The returned position corresponds to the index of the *earliest* decision point which
    /// makes the learned clause unit.
    fn find_backjump_point(&self, uip: usize) -> usize {
        let mut count_used    = 0;
        let mut backjump = uip;

        // iterating over the trail from back to front
        for cursor in (self.forced..uip+1).rev() {
            let lit = self.prop_queue[cursor];

            if self.flags[lit].is_set(Flag::IsInConflictClause) {
                count_used += 1;
            }

            if count_used == 1 && self.is_decision(lit) {
                backjump = cursor;
            }
        }

        return backjump;
    }

    // -------------------------------------------------------------------------------------------//
    // ---------------------------- RESTART ------------------------------------------------------//
    // -------------------------------------------------------------------------------------------//
    fn restart(&mut self) {
        let forced = self.forced;
        self.rollback(forced);

        self.restart_strat.set_next_limit();
        self.nb_restarts += 1;
        self.nb_conflicts = 0;
    }

    // -------------------------------------------------------------------------------------------//
    // ---------------------------- BACKTRACKING -------------------------------------------------//
    // -------------------------------------------------------------------------------------------//

    /// Rolls back the search up to the given position.
    fn rollback(&mut self, until : usize) {
        // Unravel the portion of the trail with literal that really should be rolled back
        let len = self.prop_queue.len();
        for i in (until..len).rev() {
            let lit = self.prop_queue[i];
            self.undo(lit);
        }

        // Clear the analysis of all the other literals (those who shouldn't be cancelled but whose
        // flags have been tampered with during the conflict clause analysis and recursive
        // minimization)
        for i in self.forced..until {
            let lit = self.prop_queue[i];
            self.flags[lit].reset();
        }

        // shrink the trail and reset the propagated cursor appropriately
        self.propagated = until;
        self.prop_queue.resize(until, lit(iint::max_value()));
    }

    /// Undo all state changes that have been done for some given literal
    fn undo(&mut self, lit: Literal) {
        if self.is_decision(lit) {
            self.nb_decisions -= 1;
        }

        // clear all flags
        self.flags[lit].reset();

        // clear the value & reason (and save the phase for later use)
        self.phase_saving.set_value(lit, self.valuation.get_value(lit));
        self.valuation.set_value(lit, Bool::Undef);
        self.reason[lit.var()] = None;

        // make the decision possible again
        self.var_order.push_back(lit.var());
    }

    // -------------------------------------------------------------------------------------------//
    // ---------------------------- MISC ---------------------------------------------------------//
    // -------------------------------------------------------------------------------------------//

    fn is_decision(&self, lit : Literal) -> bool {
        self.reason[lit.var()].is_none()
    }

    /// Convenience (private) method to mark and bump a literal during conflict analysis iff it has
    /// not been marked-bumped yet
    ///
    /// # Note
    /// This function is implemented as an associated function in order to get over the complaints
    /// of the borrow checker. Indeed, this fn is used in contexts where &self is already borrowed
    /// mutably/immutably. This function solves the problem by explicily mentioning which parts of
    /// the state are required to be muted.
    ///
    fn mark_and_bump(lit : Literal, nb_conflicts: uint, flags: &mut LitIdxVec<Flags>, var_order: &mut VariableOrdering ) {
        if !flags[lit].is_set(Flag::IsMarked) {
            flags[lit].set(Flag::IsMarked);
            var_order.bump(lit.var(), nb_conflicts);
        }
    }


}

// -----------------------------------------------------------------------------------------------
/// # Unit Tests
// -----------------------------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assign_yields_ok_when_lit_is_undef(){
        let mut solver = Solver::new(3);

        assert_eq!(Bool::Undef, solver.valuation.get_value(lit(1)));
        assert!(solver.assign(lit(1), None).is_ok());
    }

    #[test]
    fn assign_yields_ok_when_lit_is_true(){
        let mut solver = Solver::new(3);

        assert_eq!(Bool::Undef, solver.valuation.get_value(lit(1)));
        assert!(solver.assign(lit(1), None).is_ok());

        assert_eq!(Bool::True, solver.valuation.get_value(lit(1)));
        assert!(solver.assign(lit(1), None).is_ok());
    }

    #[test]
    fn assign_yields_err_when_lit_is_false(){
        let mut solver = Solver::new(3);

        assert_eq!(Bool::Undef, solver.valuation.get_value(lit(1)));
        assert!(solver.assign(lit(1), None).is_ok());

        assert_eq!(Bool::True, solver.valuation.get_value(lit(1)));
        assert!(solver.assign(lit(-1), None).is_err());
    }

    #[test]
    fn assign_enqueues_new_literl(){
        let mut solver = Solver::new(3);

        assert_eq!(0, solver.prop_queue.len());
        assert!(solver.assign(lit(1), None).is_ok());
        assert_eq!(1, solver.prop_queue.len());
    }

    #[test]
    fn assign_does_not_enqueue_when_literal_is_already_on_queue(){
        let mut solver = Solver::new(3);

        assert_eq!(0, solver.prop_queue.len());
        assert!(solver.assign(lit(1), None).is_ok());
        assert_eq!(1, solver.prop_queue.len());
        assert!(solver.assign(lit(1), None).is_ok());
        assert_eq!(1, solver.prop_queue.len());
    }

    #[test]
    fn assign_increases_nb_decisions_upon_new_decision() {
        let mut solver = Solver::new(3);

        assert_eq!(0, solver.nb_decisions);
        assert!(solver.assign(lit(1), None).is_ok());
        assert_eq!(1, solver.nb_decisions);
    }
    #[test]
    fn assign_does_not_change_nb_decisions_upon_propagation() {
        let mut solver = Solver::new(3);
        solver.add_problem_clause(vec![1, -2, -3]);

        assert_eq!(0, solver.nb_decisions);
        let reason = Some(solver.constraints.last().unwrap().alias());
        assert!(solver.assign(lit(1), reason).is_ok());
        assert_eq!(0, solver.nb_decisions);
    }
    #[test]
    fn assign_increases_forced_when_at_root_level() {
        let mut solver = Solver::new(3);
        solver.add_problem_clause(vec![1, -2, -3]);

        assert_eq!(0, solver.forced);
        let reason = Some(solver.constraints.last().unwrap().alias());
        assert!(solver.assign(lit(1), reason).is_ok());
        assert_eq!(1, solver.forced);
    }
    #[test]
    fn assign_does_not_change_forced_when_not_at_root_level() {
        let mut solver = Solver::new(3);
        solver.add_problem_clause(vec![1, -2, -3]);

        assert_eq!(0, solver.forced);
        assert!(solver.assign(lit(2), None).is_ok()); // decision changes the DL
        let reason = Some(solver.constraints.last().unwrap().alias()); // DL > 0 so not at root
        assert!(solver.assign(lit(1), reason).is_ok());
        assert_eq!(0, solver.forced);
    }

    #[test]
    fn assign_sets_the_value_and_reason() {
        let mut solver = Solver::new(3);
        solver.add_problem_clause(vec![1, -2, -3]);

        assert_eq!(Bool::Undef, solver.valuation.get_value(lit(1)));
        assert_eq!(Bool::Undef, solver.valuation.get_value(lit(2)));

        assert!(solver.assign(lit(2), None).is_ok()); // decision changes the DL
        let reason = Some(solver.constraints.last().unwrap().alias()); // DL > 0 so not at root
        assert!(solver.assign(lit(1), reason).is_ok());

        assert_eq!(Bool::True, solver.valuation.get_value(lit(1)));
        assert_eq!(Bool::True, solver.valuation.get_value(lit(2)));

        assert!(solver.reason[var(1)].is_some());
        assert!(solver.reason[var(2)].is_none())
    }


    #[test]
    fn decide_must_yield_all_unassigned_values(){
        let mut solver = Solver::new(3);

        solver.phase_saving.set_value(lit(1), Bool::True);
        solver.phase_saving.set_value(lit(2), Bool::True);
        solver.phase_saving.set_value(lit(3), Bool::True);

        let mut decision = solver.decide();
        assert!(decision.is_some());
        assert_eq!(lit(1), decision.unwrap());

        decision = solver.decide();
        assert!(decision.is_some());
        assert_eq!(lit(3), decision.unwrap());

        decision = solver.decide();
        assert!(decision.is_some());
        assert_eq!(lit(2), decision.unwrap());

        decision = solver.decide();
        assert!(decision.is_none());
    }

    #[test]
    fn decide_must_skip_all_assigned_values(){
        let mut solver = Solver::new(3);

        assert!(solver.assign(lit(3), None).is_ok());
        assert!(solver.assign(lit(1), None).is_ok());

        let mut decision = solver.decide();
        assert!(decision.is_some());
        assert_eq!(lit(-2), decision.unwrap());

        decision = solver.decide();
        assert!(decision.is_none());
    }

    #[test]
    fn decide_must_yield_none_when_all_vars_are_assigned(){
        let mut solver = Solver::new(3);

        assert!(solver.assign(lit(3), None).is_ok());
        assert!(solver.assign(lit(2), None).is_ok());
        assert!(solver.assign(lit(1), None).is_ok());

        assert!(solver.decide().is_none());
    }

    #[test]
    fn decide_must_return_values_in_heuristic_order(){
        let mut solver = Solver::new(3);

        solver.phase_saving.set_value(lit(1), Bool::True);
        solver.phase_saving.set_value(lit(2), Bool::True);
        solver.phase_saving.set_value(lit(3), Bool::True);

        solver.var_order.bump(var(3), 30);
        solver.var_order.bump(var(2), 20);
        solver.var_order.bump(var(1), 10);

        let mut decision = solver.decide();
        assert!(decision.is_some());
        assert_eq!(lit(3), decision.unwrap());

        decision = solver.decide();
        assert!(decision.is_some());
        assert_eq!(lit(2), decision.unwrap());

        decision = solver.decide();
        assert!(decision.is_some());
        assert_eq!(lit(1), decision.unwrap());

        decision = solver.decide();
        assert!(decision.is_none());
    }

    #[test]
    fn decide_must_return_the_saved_polarity(){
        let mut solver = Solver::new(3);
        solver.var_order.bump(var(3), 30);
        solver.var_order.bump(var(2), 20);
        solver.var_order.bump(var(1), 10);

        solver.phase_saving.set_value(lit(1), Bool::False);
        solver.phase_saving.set_value(lit(2), Bool::True);
        solver.phase_saving.set_value(lit(3), Bool::Undef);

        let mut decision = solver.decide();
        assert!(decision.is_some());
        assert_eq!(lit(-3), decision.unwrap());

        decision = solver.decide();
        assert!(decision.is_some());
        assert_eq!(lit(2), decision.unwrap());

        decision = solver.decide();
        assert!(decision.is_some());
        assert_eq!(lit(-1), decision.unwrap());

        decision = solver.decide();
        assert!(decision.is_none());
    }

    #[test]
    fn propagate_processes_everything_until_a_fixed_point_is_reached(){
        let mut solver = Solver::new(3);

        // initialize the constraint database
        solver.add_problem_clause(vec![1, -2, -3]);
        solver.add_problem_clause(vec![2, -3]);
        solver.add_problem_clause(vec![3]);

        // start the test (for real !)
        solver.assign(Literal::from(3), None).expect("3 should be assignable");

        assert_eq!(solver.propagated, 0);
        assert_eq!(solver.prop_queue, vec![lit(-3)]);

        assert!(solver.propagate().is_none());

        assert_eq!(solver.propagated, 3);
        assert_eq!(solver.prop_queue, vec![lit(-3), lit(-2), lit(-1)]);
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
        assert_eq!(solver.prop_queue, vec![lit(-3), lit(2)])
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
        solver.prop_queue.push(lit(1));

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

    #[test]
    fn rollback_saves_the_old_phase() {
        let mut solver = Solver::new(5);

        for i in 1..6 {
            let lit = lit(i);
            assert!(solver.assign(lit, None).is_ok());
            assert_eq!(Bool::Undef, solver.phase_saving.get_value(lit));
        }

        solver.rollback(3);
        for i in (4..6).rev() {
            let l = lit(i);
            assert_eq!(Bool::True , solver.phase_saving.get_value(l));
            assert_eq!(Bool::False, solver.phase_saving.get_value(!l));
        }
    }
}