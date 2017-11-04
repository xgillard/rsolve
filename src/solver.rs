use std::clone::Clone;

use super::lit;
use utils::*;
use core::*;
use flags::*;
use collections::*;
use variable_ordering::*;

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
    pub trail       : Trail,

    pub valuation   : Valuation,
    pub reason      : VarIdxVec<Option<Reason>>,

    pub constraints : Vec<Aliasable<Clause>>,
    pub learned     : Vec<Aliasable<Clause>>,

    /// Watchers: vectors of watchers associated with each literal.
    /// _Important Notice_ : A clause should watch a literal it owns, not its negation !
    pub watchers    : LitIdxVec<Vec<Watcher>>,
    /// The flags associated with each literal
    pub flags       : LitIdxVec<Flags>,
    /// The variable ordering heuristic (derivative of vsids)
    pub var_order   : VariableOrdering,

    /// The number of decisions that have been taken (so far) during the search
    pub nb_decisions: uint,
    /// The number of conflicts that have occurred since the last restart
    pub nb_conflicts: uint,
    /// The number of restarts that have occured since the very beginning
    pub nb_restarts : usize
}

impl Solver {
    pub fn new(nb_vars: usize) -> Solver {
        let mut solver = Solver {
            nb_decisions: 0,
            nb_restarts : 0,
            nb_conflicts: 0,

            constraints : vec![],
            learned     : vec![],

            valuation   : Valuation::new(nb_vars),
            reason      : VarIdxVec::with_capacity(nb_vars),
            watchers    : LitIdxVec::with_capacity(nb_vars),
            flags       : LitIdxVec::with_capacity(nb_vars),
            var_order   : VariableOrdering::new(nb_vars as uint),

            trail : Trail {
                forced    : 0,
                propagated: 0,
                prop_queue: Vec::with_capacity(nb_vars),
            }
        };

        // initialize empty watchers lists
        for _ in 0..nb_vars {
            solver.watchers.push_values(vec![], vec![]);
            solver.flags   .push_values(Flags::new(), Flags::new());

            solver.reason  .push(None);
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
    pub fn add_learned_clause(&mut self, c :Vec<Literal>) {
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
    // ---------------------------- PROPAGATION --------------------------------------------------//
    // -------------------------------------------------------------------------------------------//

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
                self.valuation.set_value(lit, Bool::True);
                self.reason[lit.var()] = reason;
                self.trail.enqueue(lit);
                Ok(())
            }
        }
    }

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
    // ---------------------------- CLAUSE LEARNING ----------------------------------------------//
    // -------------------------------------------------------------------------------------------//
    pub fn resolve_conflict(&mut self, conflicting: &Clause) -> Result<(), ()> {
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
    pub fn build_conflict_clause(&mut self, uip: usize) -> Vec<Literal> {
        let mut learned = Vec::new();

        for cusor in (self.trail.forced..uip+1).rev() {
            let lit = self.trail.prop_queue[cusor];

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
    pub fn find_first_uip(&mut self, conflicting: &Clause) -> usize {
        // mark all literals in the conflict clause
        for l in conflicting.iter() {
            Solver::mark_and_bump(*l, self.nb_conflicts, &mut self.flags, &mut self.var_order);
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

    /// Returns the position (index in `prop_queue`) until which the solver should backtrack
    /// to continue searching while incorporating the knowledge gained with learned clause
    /// implying `uip`.
    ///
    /// The returned position corresponds to the index of the *earliest* decision point which
    /// makes the learned clause unit.
    pub fn find_backjump_point(&self, uip: usize) -> usize {
        let mut count_used    = 0;
        let mut backjump = uip;

        // iterating over the trail from back to front
        for cursor in (self.trail.forced..uip+1).rev() {
            let lit = self.trail.prop_queue[cursor];

            if self.flags[lit].is_set(Flag::IsInConflictClause) {
                count_used += 1;
            }

            if count_used == 1 && self.is_decision(lit) {
                backjump = cursor;
            }
        }

        return backjump;
    }

    /// Rolls back the search up to the given position.
    pub fn rollback(&mut self, until : usize) {
        // Unravel the portion of the trail with literal that really should be rolled back
        let len = self.trail.prop_queue.len();
        for i in (until..len).rev() {
            let lit = self.trail.prop_queue[i];
            self.undo(lit);
        }

        // Clear the analysis of all the other literals (those who shouldn't be cancelled but whose
        // flags have been tampered with during the conflict clause analysis and recursive
        // minimization)
        for i in self.trail.forced..until {
            let lit = self.trail.prop_queue[i];
            self.flags[lit].reset();
        }

        // shrink the trail and reset the propagated cursor appropriately
        self.trail.propagated = until;
        self.trail.prop_queue.resize(until, lit(iint::max_value()));
    }

    /// Undo all state changes that have been done for some given literal
    pub fn undo(&mut self, lit: Literal) {
        if self.is_decision(lit) {
            self.nb_decisions -= 1;
        }

        // clear all flags
        self.flags[lit].reset();

        // clear the value & reason
        self.valuation.set_value(lit, Bool::Undef);
        self.reason[lit.var()] = None;

        // make the decision possible again
        self.var_order.push_back(lit.var());
    }

    /// Returns true iff the given `position` (index) in the trail `prop_queue` is an unique
    /// implication point (UIP). A position is an uip if:
    /// - it is a decision.
    /// - it is the last marked literal before a decision.
    pub fn is_uip(&self, position: usize) -> bool {
        let literal = self.trail.prop_queue[position];

        if self.is_decision(literal) {
            return true;
        }

        if !self.flags[literal].is_set(Flag::IsMarked) {
            return false;
        }

        for iter in (self.trail.forced..position).rev() {
            let iter_literal= self.trail.prop_queue[iter];

            if self.flags[iter_literal].is_set(Flag::IsMarked) {
                return false;
            }
            if self.is_decision(iter_literal) {
                return true;
            }
        }

        return false;
    }

    /// Convenience (private) method to mark and bump a literal during conflict analysis iff it has
    /// not been marked-bumped yet
    pub fn mark_and_bump(lit : Literal, nb_conflicts: uint, flags: &mut LitIdxVec<Flags>, var_order: &mut VariableOrdering ) {
        if !flags[lit].is_set(Flag::IsMarked) {
            flags[lit].set(Flag::IsMarked);
            var_order.bump(lit.var(), nb_conflicts);
        }
    }

    pub fn is_decision(&self, lit : Literal) -> bool {
        self.reason[lit.var()].is_none()
    }

    /// returns true iff recursive analysis showed `lit` to be implied by other literals
    pub fn is_implied(lit: Literal, flags: &mut LitIdxVec<Flags>, reason: &VarIdxVec<Option<Reason>>) -> bool {
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
}

// -----------------------------------------------------------------------------------------------
/// # Trail
/// The structure that memorizes the state and order in which literals have been assigned
// -----------------------------------------------------------------------------------------------
#[derive(Debug)]
pub struct Trail {
    pub prop_queue : Vec<Literal>,
    pub forced     : usize,
    pub propagated : usize
}

impl Trail {

    pub fn enqueue(&mut self, lit: Literal) {
        self.prop_queue.push(!lit);
    }

}