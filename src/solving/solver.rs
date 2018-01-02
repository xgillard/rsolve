use std::usize;

use core::*;
use collections::*;
use solving::*;

type  ClauseId = usize;
const CLAUSE_ELIDED: ClauseId = usize::MAX;

type Watcher  = ClauseId;
type Conflict = ClauseId;
type Reason   = ClauseId;

// -----------------------------------------------------------------------------------------------
/// # Solver
/// This structure encapsulates the state of the solver. The associated methods define the CDCL
/// solving behavior.
// -----------------------------------------------------------------------------------------------
#[derive(Debug)]
pub struct Solver {
    // ~~~ # Statistics ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    /// The number of decisions that have been taken (so far) during the search
    pub nb_decisions : uint,
    /// The number of conflicts that have occurred since the last restart
    pub nb_conflicts_since_restart: usize,
    /// The total number of conflicts that have occurred
    pub nb_conflicts: usize,
    /// The number of restarts that have occured since the very beginning
    pub nb_restarts  : usize,
    /// The number of learned clauses currently in the database
    pub nb_learned : usize,

    // ~~~ # Solver State ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    /// The current assignment of boolean values to variables
    pub valuation: Valuation,
    /// All the clauses that make the problem
    clauses : Vec<Clause>,

    /// A flag telling whether or not the solver was detected to be unsat.
    /// This flag must be set while adding clauses to the problem and during conflict resolution
    /// Whenever the flag `is_unsat` is being turned on, it becomes pointless to continue using
    /// the solver as it will always answer the same result.
    is_unsat     : bool,

    // ~~~ # Heuristics ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    /// The variable ordering heuristic (derivative of vsids)
    var_order    : VariableOrdering,
    /// The partial valuation remembering the last phase of each variable
    phase_saving : Valuation,
    /// The number of clauses that can be learned before we start to try cleaning up the database
    max_learned  : usize,
    /// The restart strategt (luby)
    restart_strat: LubyRestartStrategy,
    /// The variables that have been decided upon
    decisions    : Vec<Variable>,
    decisions_pos: Vec<usize>,
    /// The last level at which some variable was assigned
    level        : VarIdxVec<u32>,

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
            nb_conflicts_since_restart: 0,
            nb_conflicts : 0,
            nb_learned   : 0,

            valuation    : Valuation::new(nb_vars),
            clauses      : vec![],
            is_unsat     : false,

            var_order    : VariableOrdering::new(nb_vars as uint),
            phase_saving : Valuation::new(nb_vars),
            max_learned  : 1000,
            restart_strat: LubyRestartStrategy::new(1),
            decisions    : vec![],
            decisions_pos: vec![],
            level        : VarIdxVec::from(vec![0; nb_vars]),

            watchers     : LitIdxVec::with_capacity(nb_vars),
            prop_queue   : Vec::with_capacity(nb_vars),
            forced       : 0,
            propagated   : 0,

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

    // -------------------------------------------------------------------------------------------//
    // ---------------------------- CLAUSE DB MANAGEMENT -----------------------------------------//
    // -------------------------------------------------------------------------------------------//

    /// This is where we do the bulk of the work to add a clause to a clause database.
    ///
    /// # Note
    /// It was implemented as a macro in order to define this behavior only once and avoid repeating it.
    /// Nevertheless, this macro is not meant to be accessible from the outside world and you should
    /// refrain from using it. The only place where it is really legitimate to call this macro is from
    /// within `add_problem_clause` and `add_learned_clause`. The latter two are the ones you should
    /// really be using instead of the macro.
    fn add_clause(&mut self, clause: Clause) -> Result<ClauseId, ()> {
        let c_id= self.clauses.len();

        // if it is the empty clause that we're adding, the problem is solved and provably unsat
        if clause.len() == 0 {
            self.is_unsat = true;
            return Err(());
        }

        // if the clause is unit, we shouldn't watch it, it should be enough to just assert it
        if clause.len() == 1 {
            self.is_unsat |= self.assign(clause[0], Some(CLAUSE_ELIDED)).is_err();
            return if self.is_unsat { Err(())} else { Ok(CLAUSE_ELIDED) };
        }

        // -- Activate the clause --
        // clauses of size 0 and 1 are out of the way. We're certain to remain with clauses having
        // at least two literals
        let wl1 = clause[0];
        let wl2 = clause[1];

        self.clauses.push(clause);
        self.watchers[wl1].push(c_id);
        self.watchers[wl2].push(c_id);

        return Ok(c_id);
    }

    // TODO: rename post constraint ?
    pub fn add_problem_clause(&mut self, c : &mut Vec<iint>) -> Result<ClauseId, ()> {
        // don't add the clause if it is a tautology
        c.sort_unstable_by(|x, y| x.abs().cmp(&y.abs()));

        for i in (1..c.len()).rev() {
            if c[i] == -c[i-1] { return Ok(CLAUSE_ELIDED); }
        }

        let literals: Vec<Literal> = c.iter()
                                     .map(|l|Literal::from(*l))
                                     .filter(|l| !self.flags[!*l].is_set(Flag::IsForced))
                                     .collect();

        // don't add the clause if it's guaranteed to be satisfied
        for l in literals.iter() {
            if self.flags[*l].is_set(Flag::IsForced) {
                return Ok(CLAUSE_ELIDED);
            }
        }

        return self.add_clause(Clause::new(literals, false) );
    }

    fn add_learned_clause(&mut self, c :Vec<Literal>) -> Result<ClauseId, ()> {
        let result = self.add_clause(Clause::new(c, true) );

        if result.is_ok() && result.unwrap() != CLAUSE_ELIDED {
            self.nb_learned += 1;
        }

        return result;
    }

    fn remove_clause(&mut self, clause_id: ClauseId) {
        let last = self.clauses.len() - 1;

        // Remove clause_id from the watchers lists
        for i in 0..2 {
            let watched = self.clauses[clause_id][i];

            let nb_watchers = self.watchers[watched].len();
            for j in (0..nb_watchers).rev() {
                if self.watchers[watched][j] == clause_id {
                    self.watchers[watched].swap_remove(j);
                    break;
                }
            }
        }

        // Remove clause_id from the reason
        let first_variable = self.clauses[clause_id][0].var();
        match self.reason[first_variable] {
            None    => { /* nothing to do */ },
            Some(r) => {
                if r == clause_id {
                    self.reason[first_variable] = None
                }
            }
        }

        if last != clause_id {
            // Replace last by clause_id in the watchers lists
            for i in 0..2 {
                let watched = self.clauses[last][i];

                let nb_watchers = self.watchers[watched].len();
                for i in 0..nb_watchers {
                    if self.watchers[watched][i] == last {
                        self.watchers[watched][i] = clause_id;
                        break;
                    }
                }
            }

            // Replace last by clause_id in the reason
            let first_variable = self.clauses[last][0].var();
            match self.reason[first_variable] {
                None => { /* nothing to do */ },
                Some(r) => {
                    if r == last {
                        self.reason[first_variable] = Some(clause_id)
                    }
                }
            }
        }

        // Effectively remove the clause
        if self.clauses[clause_id].is_learned {
            self.nb_learned -= 1;
        }

        self.clauses.swap_remove(clause_id);
    }

    // -------------------------------------------------------------------------------------------//
    // ---------------------------- SEARCH -------------------------------------------------------//
    // -------------------------------------------------------------------------------------------//

	/// This is the core method of the solver, it determines the satisfiability of the
	/// problem through a CDCL based solving.
	///
	/// # Return Value
	/// true if there exist an assignment satisfying the given cnf problem.
	/// false if there exists no such assignment.
	///
    pub fn solve(&mut self) -> bool {
        loop {
            if self.is_unsat { return false; }

            match self.propagate() {
                Some(conflict) => {
                    self.nb_conflicts += 1;
                    self.nb_conflicts_since_restart += 1;

                    // if there is a conflict, I try to resolve it. But if I can't, that
                    // means that the problem is UNSAT
                    if self.resolve_conflict(conflict).is_err() {
                        self.is_unsat = true;
                        return false;
                    }

                    if self.nb_learned > self.max_learned {
                        self.reduce_db();
                        self.max_learned = (self.max_learned * 3) / 2;
                    }

                    if self.restart_strat.is_restart_required(self.nb_conflicts_since_restart) {
                        self.restart();
                    }
                },
                None => {
                    match self.decide() {
                        None      => return true,
                        Some(lit) => self.assign(lit, None).ok()
                    };
                }
            }
        }
    }

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
                match saved {
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
                let has_no_reason = reason.is_none();

                self.valuation.set_value(lit, Bool::True);
                self.reason[lit.var()] = reason;
                self.level [lit.var()] = self.nb_decisions;
                self.prop_queue.push(!lit);

                // if its a decision, make sure to take that into account
                if has_no_reason {
                    self.nb_decisions += 1;
                    self.decisions.push(lit.var());
                    self.decisions_pos.push(self.prop_queue.len()-1)
                }

                // if the solver is at root level, then assignment must follow from the problem
                if self.nb_decisions == 0 {
                    self.flags[lit].set(Flag::IsForced);
                    self.forced += 1;
                }

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

            if self.flags[literal].is_set(Flag::IsForced) {
                self.reason_about_literal_being_forced(literal);
            }

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
            let watcher = self.watchers[lit][i];
            self.watchers[lit].swap_remove(i);

            let new_literal_found = self.clauses[watcher].find_new_literal(lit, &self.valuation);
            match new_literal_found {
                Ok (l) => {
                    // l was found, its ok. We only need to start watching it
                    self.watchers[l].push(watcher);
                },
                Err(l) => {
                    // No result could be found, so we need to keep watching `lit`
                    self.watchers[lit].push(watcher);
                    // In the meantime we also need to assign `l`, otherwise the whole
                    // clause is going to be unsat
                    match self.assign(l, Some(watcher)) {
                        // Assignment went on well, we're done
                        Ok(()) => { },
                        // Conflict detected, return it !
                        Err(())=> return Some(watcher)
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
    /// # Note
    /// The conflict clause which is learned is immediately minimized with the so called recursive
    /// minimization technique. For further reference, please refer to
    /// * Minimizing Learned Clauses (Sörensson, Biere -- 2009)
    ///
    /// # Return Value
    /// Ok  whenever the conflict could safely be resolved,
    /// Err when the conflict could not be resolved (that is to say, when the problem is
    ///     proven to be UNSAT
    fn resolve_conflict(&mut self, conflict: ClauseId) -> Result<(), ()> {
        let uip = self.find_first_uip(conflict);
        let learned = self.build_conflict_clause(uip);
        let backjump = self.find_backjump_point(uip);

        self.rollback(backjump);

        match self.add_learned_clause(learned) {
            Err(()) => Err(()),
            Ok (c) if c == CLAUSE_ELIDED  => Ok (()),
            Ok (c_id) => {
                let asserting_lit = self.clauses[ c_id ][0];
                return self.assign(asserting_lit, Some(c_id));
            }
        }
    }

	/// This method builds a and returns minimized conflict clause by walking the marked literals
    /// to compute a cut.
    ///
	/// `uip` is the position of the 1st uip
    fn build_conflict_clause(&mut self, uip: usize) -> Vec<Literal> {
        let mut learned = Vec::new();

        for cusor in (self.forced..uip+1).rev() {
            let lit = self.prop_queue[cusor];

            if self.flags[lit].is_set(Flag::IsMarked) && !self.is_implied(lit) {
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
    fn find_first_uip(&mut self, conflict: ClauseId) -> usize {

        { // mark all literals in the conflict clause
            let ref mut conflicting = self.clauses[conflict];
            for l in conflicting.iter() {
                Solver::mark_and_bump(*l, &mut self.flags, &mut self.var_order);
            }
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
            match self.reason[lit.var()] {
                // will never happen
                None => panic!("{:?} is a decision (it has no reason), but is_uip() replied false"),
                Some(c_id) => match c_id {
                    // will not happen either
                    CLAUSE_ELIDED => {/* Ignore */},
                    // will always happen
                    reason_id => {
                        // Glucose-like database management
                        let lbd = self.literal_block_distance(reason_id);

                        let ref mut cause = self.clauses[reason_id];

                        if lbd < cause.get_lbd() {
                            cause.set_lbd(lbd);
                        }

                        for l in cause.iter().skip(1) {
                            Solver::mark_and_bump(*l, &mut self.flags, &mut self.var_order);
                        }
                    }
                }
            }
        }

        self.var_order.decay();

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
    /// # Bibliographic reference
    /// For further reference on recursive clause minimization, please refer to
    /// * Minimizing Learned Clauses (Sörensson, Biere -- 2009)
    ///
    fn is_implied(&mut self, lit: Literal) -> bool {
        // If it's already been analyzed, reuse that info
        let flags_lit = self.flags[lit];
        if flags_lit.one_of(Flag::IsImplied, Flag::IsNotImplied) {
            return flags_lit.is_set(Flag::IsImplied);
        }

        match &self.reason[lit.var()] {
            // If it's a decision, there's no way it is implied
            &None       => return false,
            &Some(c_id) => match c_id {
                // will not happen either
                CLAUSE_ELIDED => { return true; },
                // will always happen
                reason_id    => {
                    let c_len = self.clauses[reason_id].len();
                    for i in 1..c_len {
                        let l = self.clauses[reason_id][i];
                        if !self.flags[l].is_set(Flag::IsMarked) && !self.is_implied(l) {
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
    // ---------------------------- CLAUSE DATABASE REDUCTION ------------------------------------//
    // -------------------------------------------------------------------------------------------//

    /// This function tells whether or not a clause can be forgotten by the solver.
    /// Normally all clauses that are learned and not being used at the moment (not locked) can
    /// safely be forgotten by the solver. Meanwhile, this method incorporates some heuristic
    /// knowledge and keeps all the the clauses that are 'good enough'.
    fn can_forget(&self, clause_id: ClauseId) -> bool {
        let ref clause = self.clauses[clause_id];

        clause.is_learned
            && clause.get_lbd() > 2
            && clause.len() > 2
            && !self.is_locked(clause_id)
    }

    /// Forgets some of the less useful clauses to speed up the propagation process.
    fn reduce_db(&mut self) {
        // sort the clauses according to their heuristic quality score (LBD)
        let nb_clauses = self.clauses.len();
        let mut remove_agenda: Vec<ClauseId> = (0..nb_clauses)
            .filter(|id| self.can_forget(*id))
            .collect();

        remove_agenda.sort_unstable_by_key(|c| self.clauses[*c].get_lbd());
        remove_agenda.reverse();

        // reduces the size of the database by removing half of the worst clauses.
        // It should be noted though that unary and binary clauses are *never* removed
        // and that 'locked' clauses (those who are reason for some assignment) are kept as well
        let limit = self.nb_learned / 2;
        remove_agenda.truncate(limit);

        // Actually proceed to the clause deletion
        let nb_delete = remove_agenda.len();
        for i in 0..nb_delete {
            let id = remove_agenda[i];
            let last   = self.clauses.len()-1;

            self.remove_clause(id);

            // Because remove_clause might have swapped `id` and `last`, we need to fix that up in
            // the agenda (to avoid panicking on out of bounds index)
            if id != last {
                for j in i+1..nb_delete {
                    if remove_agenda[j] == last {
                        remove_agenda[j] = id;
                    }
                }
            }
        }
    }

    /// Returns true iff the given clause (alias) is used as the reason of some unit propagation
    /// in the current assignment
    fn is_locked(&self, clause_id: ClauseId) -> bool {
        let ref clause = self.clauses[clause_id];
        if clause.len() < 2 { return true; }

        let lit = clause[0];
        if self.valuation.is_undef(lit) {
            return false;
        } else {
            let reason = self.reason[lit.var()];

            return match reason {
                None    => false,
                Some(x) => x == clause_id
            }
        }
    }

    /// Computes the literal block distance (LBD) of some clause.
    fn literal_block_distance(&self, clause_id: ClauseId) -> u32 {
        // Shortcut: Having an LBD of two means it is a glue clause. It will never be deleted so
        // hence there is no point in recomputing it every time as it is not going to be improved.
        let ref clause = self.clauses[clause_id];
        if clause.get_lbd() <= 2 { return clause.get_lbd(); }

        let mut min_level = 0;
        let mut max_level = 0;

        for lit in clause.iter() {
            let level = self.level[lit.var()];

            if level < min_level {
                min_level = level;
            }
            if level > max_level {
                max_level = level;
            }
        }

        return max_level - min_level;
    }

    // -------------------------------------------------------------------------------------------//
    // ---------------------------- RESTART ------------------------------------------------------//
    // -------------------------------------------------------------------------------------------//

    /// Implements a partial restart that tries to avoid redoing unnecessary decisions-propagations
    /// by reusing the current assignment trail. For further reference, please refer to :
    /// * Reusing the Assignment Trail in CDCL solvers (Van Der Tak, Ramos, Heule -- 2011)
    /// * Between Restarts and Backjumps (Ramos, Van Der Tak, Heule -- 2011)
    fn restart(&mut self) {
        match self.find_partial_restart_pos() {
            None => return,
            Some(position) => {
                self.rollback(position);

                self.restart_strat.set_next_limit();
                self.nb_restarts += 1;
                self.nb_conflicts_since_restart = 0;
            }
        }
    }

    /// Finds the position as of which the trail will not be reused when using the partial restart
    /// strategy (reused trail) described in:
    /// * Reusing the Assignment Trail in CDCL solvers (Van Der Tak, Ramos, Heule -- 2011)
    ///
    /// # Return Value
    /// The index (position == usize) of the first variable that will not be part of the reused
    /// trail. It returns None when there are no decisions that can be made (that is to say, when
    /// the trail will be integrally reused).
    fn find_partial_restart_pos(&mut self) -> Option<usize> {
        match self.peek_next_decision_var() {
            None => None,
            Some(next_var) => {
                let next_score = self.var_order.get_score(next_var);
                let mut position= self.prop_queue.len();

                for i in 0..self.decisions.len() {
                    let decision = self.decisions[i];
                    if next_score > self.var_order.get_score(decision) {
                        position = self.decisions_pos[i];
                        break;
                    }
                }

                Some(position)
            }
        }
    }

    /// finds the next variable that would have been assigned if we performed a full restart
    fn peek_next_decision_var(&mut self) -> Option<Variable> {
        let mut result = None;
        let mut undo_stack = vec![];

        // find the next (unassigned) decision variable
        while !self.var_order.is_empty() {
            let variable = self.var_order.pop_top();
            let positive = Literal::positive(variable);

            undo_stack.push(variable);
            if self.valuation.is_undef(positive) {
                result = Some(variable);
                break;
            }
        }

        // leave the var_order in the same state as it was before entering this method
        for v in undo_stack {
            self.var_order.push_back(v);
        }

        return result;
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

            // TODO maybe assert that popped value == lit.var()
            //assert_eq!(self.decisions.pop(), Some(lit.var()));
            self.decisions.pop();
            self.decisions_pos.pop();
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
    fn mark_and_bump(lit : Literal, flags: &mut LitIdxVec<Flags>, var_order: &mut VariableOrdering ) {
        if !flags[lit].is_set(Flag::IsMarked) {
            flags[lit].set(Flag::IsMarked);
            var_order.bump(lit.var() );
        }
    }

    // -------------------------------------------------------------------------------------------//
    // ---------------------------- REASONING ----------------------------------------------------//
    // -------------------------------------------------------------------------------------------//

    /// A very simple form of simplification:
    /// - whenever a clause contains a literal which is forced, this clause is guaranteed to remain
    ///   true forever. Hence it can be removed.
    /// - whenever a clause contains the negation of a literal which is forced, that literal can be
    ///   removed from the clause.
    fn reason_about_literal_being_forced(&mut self, lit: Literal) {
        let db_size = self.clauses.len();

        for id in (0..db_size).rev() {
            // If it's locked, we keep it for further reference. But if it is not, we drop the clause
            if !self.is_locked(id) && self.clauses[id].contains(&lit) {
                self.remove_clause(id);
                continue;
            }

            // When the literal is failed, we try to shrink the database
            let failed = !lit;
            if self.clauses[id].contains(&failed) {
                self.remove_failed_lit_from_clause(failed, id);
            }
        }
    }


    fn remove_failed_lit_from_clause(&mut self, failed : Literal, clause_id: ClauseId) {
        { // A. Effectively remove the failed literal from the clause
            let ref mut clause = self.clauses[clause_id];
            let c_len = clause.len();

            // First, we make sure that the failed lit is not watched
            if c_len > 1 {
                let watched: Vec<Literal> = clause.iter()
                    .take(2)
                    .map(|l| *l)
                    .collect();
                for wl in watched {
                    if wl == failed {
                        match clause.find_new_literal(failed, &self.valuation) {
                            Err(l) if l == failed => {
                                self.is_unsat = true;
                                return;
                            },
                            _ => {},
                        }
                    }
                }
            }

            // then we shrink the clause
            for j in (0..c_len).rev() {
                if clause[j] == failed {
                    clause.swap_remove(j);
                    break;
                }
            }
        }

        { // B. Perform additional checks on the modified clause
            // check whether the clause has become unit
            let c_len = self.clauses[clause_id].len();
            if c_len == 1 {
                let assertion = self.clauses[clause_id][0];
                self.is_unsat |= self.assign(assertion, Some(clause_id)).is_err();
            }
            // check whether shrinking the clause made the problem unsat
            if c_len == 0 {
                self.is_unsat = true;
                return;
            }
        }
    }

}

// -----------------------------------------------------------------------------------------------
/// # Unit Tests
// -----------------------------------------------------------------------------------------------
#[cfg(test)]
#[allow(unused_must_use)]
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
        solver.add_problem_clause(&mut vec![1, -2, -3]);

        assert_eq!(0, solver.nb_decisions);
        let reason = Some(0);
        assert!(solver.assign(lit(1), reason).is_ok());
        assert_eq!(0, solver.nb_decisions);
    }
    #[test]
    fn assign_increases_forced_when_at_root_level() {
        let mut solver = Solver::new(3);
        solver.add_problem_clause(&mut vec![1, -2, -3]);

        assert_eq!(0, solver.forced);
        let reason = Some(0);
        assert!(solver.assign(lit(1), reason).is_ok());
        assert_eq!(1, solver.forced);
    }
    #[test]
    fn assign_does_not_change_forced_when_not_at_root_level() {
        let mut solver = Solver::new(3);
        solver.add_problem_clause(&mut vec![1, -2, -3]);

        assert_eq!(0, solver.forced);
        assert!(solver.assign(lit(2), None).is_ok()); // decision changes the DL
        let reason = Some(0); // DL > 0 so not at root
        assert!(solver.assign(lit(1), reason).is_ok());
        assert_eq!(0, solver.forced);
    }

    #[test]
    fn assign_sets_the_value_and_reason() {
        let mut solver = Solver::new(3);
        solver.add_problem_clause(&mut vec![1, -2, -3]);

        assert_eq!(Bool::Undef, solver.valuation.get_value(lit(1)));
        assert_eq!(Bool::Undef, solver.valuation.get_value(lit(2)));

        assert!(solver.assign(lit(2), None).is_ok()); // decision changes the DL
        let reason = Some(0); // DL > 0 so not at root
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

        solver.var_order.bump(var(1));
        solver.var_order.decay();
        solver.var_order.bump(var(2));
        solver.var_order.decay();
        solver.var_order.bump(var(3));

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
        solver.var_order.bump(var(1));
        solver.var_order.decay();
        solver.var_order.bump(var(2));
        solver.var_order.decay();
        solver.var_order.bump(var(3));

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
        solver.add_problem_clause(&mut vec![1, -2, -3]);
        solver.add_problem_clause(&mut vec![2, -3]);
        solver.add_problem_clause(&mut vec![3]);

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
        solver.add_problem_clause(&mut vec![ 1, -2, -3]);
        solver.add_problem_clause(&mut vec![ 2, -3]);
        solver.add_problem_clause(&mut vec![ 3]);
        solver.add_problem_clause(&mut vec![-2]);

        // start the test (for real !)
        solver.assign(Literal::from( 3), None).expect(" 3 should be assignable");
        // if I propagated here, then -2 shouldn't be assignable anymore
        solver.assign(Literal::from(-2), None).expect("-2 should be assignable");

        let conflict = solver.propagate();
        assert_eq!(Some(1), conflict);
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
        solver.add_problem_clause(&mut vec![ 1,-8, 3]); // c0
        solver.add_problem_clause(&mut vec![ 1, 4,-5]); // c1
        solver.add_problem_clause(&mut vec![ 5,-6, 7]); // c2
        solver.add_problem_clause(&mut vec![ 6, 2, 7]); // c3
        solver.add_problem_clause(&mut vec![ 4,-7]);    // c4
        solver.add_problem_clause(&mut vec![-2, 8]);    // c5
        solver.add_problem_clause(&mut vec![-8,-3]);    // c6

        assert_eq!(Ok(()), solver.assign(lit(-1), None));
        assert_eq!(Ok(()), solver.assign(lit(-4), None));

        let conflict = solver.propagate();
        assert!(conflict.is_some());
        assert_eq!(format!("{:?}", 6),
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
        solver.add_problem_clause(&mut vec![ 1,-8, 3]); // c0
        solver.add_problem_clause(&mut vec![ 1, 4,-5]); // c1
        solver.add_problem_clause(&mut vec![ 5,-6, 7]); // c2
        solver.add_problem_clause(&mut vec![ 6, 2, 7]); // c3
        solver.add_problem_clause(&mut vec![ 4,-7]);    // c4
        solver.add_problem_clause(&mut vec![-2, 8]);    // c5
        solver.add_problem_clause(&mut vec![-8,-3]);    // c6

        assert_eq!(Ok(()), solver.assign(lit(-1), None));
        assert_eq!(Ok(()), solver.assign(lit(-4), None));

        let conflict = solver.propagate();

        assert!(conflict.is_some());
        assert_eq!(Some(6), conflict);
        assert_eq!(6, solver.find_first_uip(conflict.unwrap()));
        // note: is_uip() *must* be tested *after* find_first_uip() because the former method
        //       is the one setting the IsMarked flag
        assert!(solver.is_uip(6));
    }

    // isUIP must be false when the literal is not false/marked
    #[test]
    fn is_uip_must_be_false_when_literal_is_not_false() {
        let mut solver = Solver::new(8);
        solver.add_problem_clause(&mut vec![1]);

        // simulate clause activation
        let reason = 0;
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
        solver.add_problem_clause(&mut vec![ 1,-8, 3]); // c0
        solver.add_problem_clause(&mut vec![ 1, 4,-5]); // c1
        solver.add_problem_clause(&mut vec![ 5,-6, 7]); // c2
        solver.add_problem_clause(&mut vec![ 6, 2, 7]); // c3
        solver.add_problem_clause(&mut vec![ 4,-7]);    // c4
        solver.add_problem_clause(&mut vec![-2, 8]);    // c5
        solver.add_problem_clause(&mut vec![-8,-3]);    // c6

        assert_eq!(Ok(()), solver.assign(lit(-1), None));
        assert_eq!(Ok(()), solver.assign(lit(-4), None));

        let conflict = solver.propagate();
        assert!(conflict.is_some());
        assert_eq!(Some(6), conflict);

        assert_eq!(6, solver.find_first_uip(conflict.unwrap()));
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
        solver.add_problem_clause(&mut vec![ 1,-8, 3]); // c0
        solver.add_problem_clause(&mut vec![ 1, 4,-5]); // c1
        solver.add_problem_clause(&mut vec![ 5,-6, 7]); // c2
        solver.add_problem_clause(&mut vec![ 6, 2, 7]); // c3
        solver.add_problem_clause(&mut vec![ 4,-7]);    // c4
        solver.add_problem_clause(&mut vec![-2, 8]);    // c5
        solver.add_problem_clause(&mut vec![-8,-3]);    // c6

        assert_eq!(Ok(()), solver.assign(lit(-1), None));
        assert_eq!(Ok(()), solver.assign(lit(-4), None));

        let conflict = solver.propagate();

        assert!(conflict.is_some());
        assert_eq!(Some(6), conflict);
        assert_eq!(6, solver.find_first_uip(conflict.unwrap()));
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

        solver.add_problem_clause(&mut vec![ 1, 2,-3]);
        solver.add_problem_clause(&mut vec![ 1, 2,-4]);
        solver.add_problem_clause(&mut vec![ 3, 4,-5]);
        solver.add_problem_clause(&mut vec![ 3, 4, 5]);

        assert!(solver.assign(lit(-1), None).is_ok());
        assert!(solver.assign(lit(-2), None).is_ok());

        let conflict = solver.propagate();
        assert!(conflict.is_some());
        assert_eq!(Some(2), conflict); // [3, 4, -5]
        assert_eq!(1, solver.find_first_uip(conflict.unwrap()));
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

        solver.add_problem_clause(&mut vec![ 1, 2,-3]);
        solver.add_problem_clause(&mut vec![ 3,-4]);
        solver.add_problem_clause(&mut vec![ 3,-5]);
        solver.add_problem_clause(&mut vec![ 4, 5, 6]);
        solver.add_problem_clause(&mut vec![ 4, 5,-6]);

        assert!(solver.assign(lit(-1), None).is_ok());
        assert!(solver.assign(lit(-2), None).is_ok());

        let conflict = solver.propagate();
        assert!(conflict.is_some());
        assert_eq!(Some(3), conflict); // [4, 5, 6]
        assert_eq!(2, solver.find_first_uip(conflict.unwrap()));
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
        solver.add_problem_clause(&mut vec![ 1,-8, 3]); // c0
        solver.add_problem_clause(&mut vec![ 1, 4,-5]); // c1
        solver.add_problem_clause(&mut vec![ 5,-6, 7]); // c2
        solver.add_problem_clause(&mut vec![ 6, 2, 7]); // c3
        solver.add_problem_clause(&mut vec![ 4,-7]);    // c4
        solver.add_problem_clause(&mut vec![-2, 8]);    // c5
        solver.add_problem_clause(&mut vec![-8,-3]);    // c6

        assert_eq!(Ok(()), solver.assign(lit(-1), None));
        assert_eq!(Ok(()), solver.assign(lit(-4), None));

        let conflict = solver.propagate();
        let uip = solver.find_first_uip(conflict.unwrap());
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

        solver.add_problem_clause(&mut vec![ 1, 2,-3]);
        solver.add_problem_clause(&mut vec![ 1, 2,-4]);
        solver.add_problem_clause(&mut vec![ 3, 4,-5]);
        solver.add_problem_clause(&mut vec![ 3, 4, 5]);

        assert!(solver.assign(lit(-1), None).is_ok());
        assert!(solver.assign(lit(-2), None).is_ok());

        let conflict = solver.propagate();
        let uip = solver.find_first_uip(conflict.unwrap());
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

        solver.add_problem_clause(&mut vec![ 1, 2,-3]);
        solver.add_problem_clause(&mut vec![ 3,-4]);
        solver.add_problem_clause(&mut vec![ 3,-5]);
        solver.add_problem_clause(&mut vec![ 4, 5, 6]);
        solver.add_problem_clause(&mut vec![ 4, 5,-6]);

        assert!(solver.assign(lit(-1), None).is_ok());
        assert!(solver.assign(lit(-2), None).is_ok());

        let conflict = solver.propagate();
        let uip = solver.find_first_uip(conflict.unwrap());
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

        solver.add_problem_clause(&mut vec![ 1, 2,-3]);
        solver.add_problem_clause(&mut vec![ 1, 2,-4]);
        solver.add_problem_clause(&mut vec![ 3, 4,-5]);
        solver.add_problem_clause(&mut vec![ 1, 5, 6]);
        solver.add_problem_clause(&mut vec![ 2, 5,-6]);

        assert!(solver.assign(lit(-1), None).is_ok());
        assert!(solver.assign(lit(-2), None).is_ok());

        let conflict = solver.propagate();
        let uip = solver.find_first_uip(conflict.unwrap());
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

        solver.add_problem_clause(&mut vec![ 1,-4]);
        solver.add_problem_clause(&mut vec![ 2,-3]);

        solver.add_problem_clause(&mut vec![ 3, 4, 5]);
        solver.add_problem_clause(&mut vec![ 3, 1,-5]);

        assert!(solver.assign(lit(-1), None).is_ok());
        assert!(solver.propagate().is_none());

        assert!(solver.assign(lit(-2), None).is_ok());
        let conflict = solver.propagate();
        assert!(conflict.is_some());

        let uip = solver.find_first_uip(conflict.unwrap());
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

        solver.add_problem_clause(&mut vec![ 1, 2,-3]);
        solver.add_problem_clause(&mut vec![ 3,-4]);
        solver.add_problem_clause(&mut vec![ 3,-5]);
        solver.add_problem_clause(&mut vec![ 4, 5, 6]);
        solver.add_problem_clause(&mut vec![ 4, 5,-6]);

        assert!(solver.assign(lit(-1), None).is_ok());
        assert!(solver.assign(lit(-2), None).is_ok());

        let conflict = solver.propagate();
        let uip = solver.find_first_uip(conflict.unwrap());
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

        solver.add_problem_clause(&mut vec![ 1,-4]);
        solver.add_problem_clause(&mut vec![ 2,-3]);

        solver.add_problem_clause(&mut vec![ 3, 4, 5]);
        solver.add_problem_clause(&mut vec![ 3, 1,-5]);

        assert!(solver.assign(lit(-1), None).is_ok());
        assert!(solver.propagate().is_none());

        assert!(solver.assign(lit(-2), None).is_ok());
        let conflict = solver.propagate();
        assert!(conflict.is_some());

        let uip = solver.find_first_uip(conflict.unwrap());
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

        solver.add_problem_clause(&mut vec![ 1,-4]);
        solver.add_problem_clause(&mut vec![ 2,-3]);

        solver.add_problem_clause(&mut vec![ 3, 4, 5]);
        solver.add_problem_clause(&mut vec![ 3, 1,-5]);

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

        let uip = solver.find_first_uip(conflict.unwrap());
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


    #[test]
    fn solve_must_be_true_when_problem_is_vacuously_satisfiable(){
        let mut solver = Solver::new(5);

        assert!(solver.solve());
    }

    #[test]
    fn solve_must_be_true_when_problem_is_trivially_satisfiable(){
        let mut solver = Solver::new(5);
        solver.add_problem_clause(&mut vec![1, 2, 3, 4, 5]);
        assert!(solver.solve());
    }

    #[test]
    fn solve_must_be_true_when_problem_is_satisfiable_not_trivially(){
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

        solver.add_problem_clause(&mut vec![1, -4]);
        solver.add_problem_clause(&mut vec![2, -3]);

        solver.add_problem_clause(&mut vec![3, 4, 5]);
        solver.add_problem_clause(&mut vec![3, 1,-5]);

        solver.var_order.bump(var(2));
        solver.var_order.decay();
        solver.var_order.bump(var(1));

        assert!(solver.solve());
        assert_eq!(solver.nb_conflicts_since_restart, 1);
    }

    #[test]
    fn solve_must_be_true_when_problem_is_vacuously_true(){
        let mut solver = Solver::new(0);
        let satisfiable = solver.solve();
        assert!(satisfiable);
    }

    #[test]
    fn solve_must_be_false_when_problem_is_explicitly_unsat_empty_problem(){
        let mut solver = Solver::new(0);
        solver.add_problem_clause(&mut vec![]);

        let satisfiable = solver.solve();
        assert!(!satisfiable);
    }

    #[test]
    fn solve_must_be_false_when_problem_is_explicitly_unsat_nonempty_problem(){
        let mut solver = Solver::new(5);
        solver.add_problem_clause(&mut vec![1, 2, -3, 4]);
        solver.add_problem_clause(&mut vec![]);

        let satisfiable = solver.solve();
        assert!(!satisfiable);
    }

    #[test]
    fn solve_must_be_false_when_problem_is_trivially_unsat(){
        let mut solver = Solver::new(5);
        solver.add_problem_clause(&mut vec![1, 2]);
        solver.add_problem_clause(&mut vec![-1]);
        solver.add_problem_clause(&mut vec![-2]);
        assert!(!solver.solve());
    }

    #[test]
    fn solve_must_be_false_when_problem_is_not_trivially_unsat(){
        let mut solver = Solver::new(6);
        solver.add_problem_clause(&mut vec![ 3, 1]);
        solver.add_problem_clause(&mut vec![-1, 4]);
        solver.add_problem_clause(&mut vec![-1,-4]);

        solver.add_problem_clause(&mut vec![ 5, 2]);
        solver.add_problem_clause(&mut vec![-2, 6]);
        solver.add_problem_clause(&mut vec![-2,-6]);

        solver.add_problem_clause(&mut vec![ 1, 2]);

        solver.var_order.bump(var(3));
        solver.var_order.decay();
        solver.var_order.bump(var(5));

        assert!(!solver.solve());
    }

    #[test]
    fn is_locked_must_be_false_when_the_clause_is_not_the_reason_of_any_assignment(){
        let mut solver = Solver::new(3);
        solver.add_problem_clause(&mut vec![-1,-2,-3]);

        let clause = get_last_constraint(&solver);
        assert_eq!(false, solver.is_locked(clause));
    }

    #[test]
    fn is_locked_must_be_true_when_the_clause_is_the_reason_of_some_assignment(){
        let mut solver = Solver::new(3);
        solver.add_problem_clause(&mut vec![-1,-2,-3]);

        let clause = get_last_constraint(&solver);
        assert!(solver.assign(lit(2), None).is_ok());
        assert!(solver.assign(lit(3), None).is_ok());
        assert!(solver.assign(lit(-1), Some(clause)).is_ok());
        assert_eq!(true, solver.is_locked(clause));
    }

    #[test]
    fn is_locked_must_be_false_after_the_reason_has_been_reset(){
        let mut solver = Solver::new(3);
        solver.add_problem_clause(&mut vec![-1,-2,-3]);

        let clause = get_last_constraint(&solver);
        assert!(solver.assign(lit(2), None).is_ok());
        assert!(solver.assign(lit(3), None).is_ok());
        assert!(solver.assign(lit(-1), Some(clause)).is_ok());
        assert_eq!(true, solver.is_locked(clause));
        solver.rollback(0);
        assert_eq!(false, solver.is_locked(clause));
    }

    #[test]
    // This scenario is contrived, it does not respect what a solver would normally do (learned
    // clauses do not derive from the original problem statement)
    fn reduce_db_removes_worst_clauses(){
        let mut solver = Solver::new(5);
        solver.add_learned_clause(vec![lit(1), lit(2), lit(3), lit(4), lit(5)]);
        solver.add_learned_clause(vec![lit(1), lit(2)]);

        solver.clauses[0].set_lbd(5); // should be dropped
        solver.clauses[1].set_lbd(3); // should be kept

        assert!(solver.assign(lit(1), None).is_ok());

        assert_eq!(2, solver.clauses.len());
        solver.reduce_db();
        assert_eq!(1, solver.clauses.len());
        assert_eq!("Clause([Literal(1), Literal(2)])", format!("{:?}", solver.clauses[0]));
    }

    #[test]
    // This scenario is contrived, it does not respect what a solver would normally do (learned
    // clauses do not derive from the original problem statement). Additionally, it makes a clause
    // be the reason for the assignment of some literal while this would never happen in practice.
    // Nevertheless, it lets me test what I intend to test (and just that!)
    fn reduce_db_does_not_remove_locked_clauses(){
        let mut solver = Solver::new(5);
        solver.add_learned_clause(vec![lit(2), lit(1), lit(3), lit(4), lit(5)]);
        solver.add_learned_clause(vec![lit(1), lit(2), lit(3)]);

        solver.clauses[0].set_lbd(5); // should be dropped, but it is locked
        solver.clauses[1].set_lbd(2); // should be kept

        assert!(solver.assign(lit(1), None   ).is_ok());
        assert!(solver.assign(lit(2), Some(0)).is_ok());

        assert!(solver.is_locked(0));
        assert_eq!(2, solver.clauses.len());
        solver.reduce_db();
        assert_eq!(2, solver.clauses.len());
    }

    #[test]
    fn reduce_db_does_not_impact_problem_clauses(){
        let mut solver = Solver::new(5);
        solver.add_problem_clause(&mut vec![2, 3, 4, 5]);
        solver.add_learned_clause(vec![lit(1), lit(3), lit(4)]);
        solver.add_learned_clause(vec![lit(1), lit(3), lit(5)]);

        solver.clauses[0].set_lbd(18); // should be removed but it is a problem clause
        solver.clauses[1].set_lbd(5);  // must be dropped
        solver.clauses[2].set_lbd(4);  // must be kept

        assert!(solver.assign(lit(1), None).is_ok());

        assert_eq!(3, solver.clauses.len());
        solver.reduce_db();
        assert_eq!(2, solver.clauses.len());
        assert!(! solver.clauses[0].is_learned);
    }

    #[test]
    fn reduce_db_does_not_remove_clauses_of_size_2_or_less(){
        let mut solver = Solver::new(5);
        solver.add_learned_clause(vec![lit(1), lit(3)]);
        solver.add_learned_clause(vec![lit(2), lit(3)]);
        solver.add_learned_clause(vec![lit(4), lit(3)]);
        solver.add_learned_clause(vec![lit(5), lit(3)]);
        solver.add_learned_clause(vec![lit(3)]); // ELIDED

        assert_eq!(4, solver.clauses.len());
        solver.reduce_db();
        assert_eq!(4, solver.clauses.len());
    }

    #[test]
    fn reduce_db_tries_to_removes_half_of_the_clauses(){
        let mut solver = Solver::new(5);
        solver.add_learned_clause(vec![lit(1), lit(3), lit(5)]);
        solver.add_learned_clause(vec![lit(2), lit(3), lit(5)]);
        solver.add_learned_clause(vec![lit(4), lit(3), lit(5)]);

        assert_eq!(3, solver.clauses.len());
        solver.reduce_db();
        assert_eq!(2, solver.clauses.len());
    }

    fn get_last_constraint(solver : &Solver) -> ClauseId {
        solver.clauses.len() - 1
    }
}