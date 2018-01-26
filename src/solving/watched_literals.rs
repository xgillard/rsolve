use core::*;
use collections::*;

use super::*;

#[must_use]
#[derive(Debug, PartialEq)]
pub enum ActivationStatus {
    FoundTwoWatchers,
    UnitDetected(Literal),
    ConflictDetected
}

pub trait WatchedLiterals : ClauseDatabase + Valuation {
    /// Returns a reference to the vector (indexed by literals) which contains the watchers list
    /// associated with each literal.
    fn get_watchers_list    (&self)     -> &    LitIdxVec<Vec<Watcher>>;

    /// Returns a mutable reference to the vector (indexed by literals) which contains the watchers
    /// list associated with each literal.
    fn get_watchers_list_mut(&mut self) -> &mut LitIdxVec<Vec<Watcher>>;

    /// Returns a reference to the list of clauses watching the given literal
    #[inline]
    fn get_watchers(&self, lit: Literal) -> &[Watcher] {
        &self.get_watchers_list()[lit]
    }

    /// Returns a mutable reference to the list of clauses watching the given literal
    #[inline]
    fn get_watchers_mut(&mut self, lit: Literal) -> &mut Vec<Watcher> {
        &mut self.get_watchers_list_mut()[lit]
    }

    /// Tries to find a new literal that can be watched by the given clause.
    ///
    /// # Return Value
    /// This function returns a Result<Literal, Literal> that mut be interpreted as follows:
    /// - Ok( l ) means that the clause found that l is not satisfied and can therefore be
    ///           watched by the current clause.
    /// - Err(l ) means that no new literals is available to be watched. Hence, l is the last
    ///           literal that can possibly satisfy the clause. If that literal is True or
    ///           Unassigned, then the clause is unit. Otherwise, the clause is conflicting and a
    ///           conflict resolution procedure should be started
    fn find_new_literal(&mut self, c_id: ClauseId, watched: Literal) -> Result<Literal, Literal> {
        // Make sure that other WL is at position zero. This way, whenever the clause
        // becomes unit, we are certain to respect invariant B.
        if watched == self.get_clause(c_id)[0] {
            self.get_clause_mut(c_id).swap(0, 1);
        }

        let other = self.get_clause(c_id)[0];

        // If the clause is already satsified, we don't need to do anything
        if self.is_true(other) { return Ok(watched); }

        let clause_len = self.get_clause(c_id).len();
        for i in 2..clause_len {
            let lit = self.get_clause(c_id)[i];

            // not False <==> True or Unassigned
            if !self.is_false(lit) {
                // enforce invariant A
                self.get_clause_mut(c_id).swap(1, i);
                // tell that we need to start watching lit
                return Ok(lit);
            }
        }

        // We couldn't find any new literal to watch. Hence the clause is unit (under
        // the current assignment) or conflicting.
        return Err(other);
    }


    /// Activate the given clause. That is to say, it finds two literals to be watched by the clause
    /// and starts watching them.
    ///
    /// # Note
    /// It is assumed that clauses of size 0 and 1 are out of the way and we're certain to be left
    /// only with clauses having at least two literals.
    fn activate_clause(&mut self, c_id : ClauseId) -> ActivationStatus {
        let mut cnt = 0;

        let mut wl1 = self.get_clause(c_id)[0];
        let mut pl1 = 0;

        let mut wl2 = self.get_clause(c_id)[1];
        let mut pl2 = 1;

        {
            let mut watchables = self.get_clause(c_id).iter()
                .enumerate()
                .filter(|&(_, &l)| !self.is_false(l));

            if let Some((p,&l)) = watchables.next() {
                // avoid the possible case where both wl1 and wl2 designate the same literal
                if l == wl2 { wl2 = wl1; pl2 = pl1 }

                wl1 =  l;
                pl1 =  p;
                cnt += 1;
            }

            if let Some((p,&l)) = watchables.next() {
                wl2 =  l;
                pl2 =  p;
                cnt += 1;
            }
        }

        // we couldn't find any literal that can possibly be watched
        if cnt == 0 {
            return ActivationStatus::ConflictDetected;
        }

        // anyhow, remember that we must watch wl1 and wl2
        self.get_clause_mut(c_id).swap(0, pl1);
        self.get_clause_mut(c_id).swap(1, pl2);

        self.get_watchers_mut(wl1).push(c_id);
        self.get_watchers_mut(wl2).push(c_id);

        if cnt == 1 {
            // the clause is unit (under assignment) so we need to assert wl1.
            // this is going to work since we know that wl1 is watchable
            return ActivationStatus::UnitDetected(wl1);
        } else {
            return ActivationStatus::FoundTwoWatchers;
        }
    }

    /// Deactivate the given clause. That is to say, it removes all watches for the given clause.
    ///
    /// # Note
    /// It is assumed that clauses of size 0 and 1 are out of the way and we're certain to be left
    /// only with clauses having at least two literals.
    fn deactivate_clause(&mut self, c_id: ClauseId) {
        for i in 0..2 {
            let watched = self.get_clause(c_id)[i];

            let nb_watchers = self.get_watchers(watched).len();
            for j in (0..nb_watchers).rev() {
                if self.get_watchers(watched)[j] == c_id {
                    self.get_watchers_mut(watched).swap_remove(j);
                    break;
                }
            }
        }
    }
}

// -----------------------------------------------------------------------------------------------
/// # Unit Tests
// -----------------------------------------------------------------------------------------------
#[cfg(test)]
#[allow(unused_variables, unused_mut, unused_must_use)]
mod tests {
    use super::*;

    struct Dummy {
        clauses      : Vec<Clause>,
        valuation_dta: VarIdxVec<Bool>,
        watchers_list: LitIdxVec<Vec<Watcher>>,
    }

    impl Dummy {
        fn new(nb_vars: usize) -> Dummy {
            let mut ret = Dummy {
                clauses       : vec![],
                valuation_dta : VarIdxVec::from(vec![Bool::Undef; nb_vars]),
                watchers_list : LitIdxVec::with_capacity(nb_vars)
            };
            for _ in 0..nb_vars { ret.watchers_list.push_values(vec![], vec![]) }
            return ret;
        }
    }

    impl ClauseDatabase for Dummy {
        fn add_clause(&mut self, c: Clause) -> Result<ClauseId, ()> {
            self.clauses.push(c);
            Ok(self.clauses.len())
        }

        fn remove_clause(&mut self, c_id: ClauseId) {
            unimplemented!()
        }

        fn get_clauses(&self) -> &[Clause] {
            &self.clauses
        }

        fn get_clauses_mut(&mut self) -> &mut Vec<Clause> {
            &mut self.clauses
        }
    }

    impl Valuation for Dummy {
        fn get_valuation_data(&self) -> &VarIdxVec<Bool> {
            &self.valuation_dta
        }

        fn get_valuation_data_mut(&mut self) -> &mut VarIdxVec<Bool> {
            &mut self.valuation_dta
        }
    }

    impl WatchedLiterals for Dummy {
        fn get_watchers_list(&self) -> &LitIdxVec<Vec<Watcher>> {
            &self.watchers_list
        }

        fn get_watchers_list_mut(&mut self) -> &mut LitIdxVec<Vec<Watcher>> {
            &mut self.watchers_list
        }
    }

    #[test]
    fn find_new_literal_does_nothing_if_the_clause_is_already_sat(){
        let mut dummy= Dummy::new(8);

        dummy.set_value(lit(1), Bool::True);
        dummy.set_value(lit(2), Bool::False);
        dummy.set_value(lit(4), Bool::False);
        dummy.set_value(lit(8), Bool::Undef);

        // create the tested clause
        let mut clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        dummy.add_clause(clause);

        let watched = Literal::from(2);
        assert_eq!(dummy.find_new_literal(0, watched), Ok(Literal::from(2)))
    }


    #[test]
    fn find_new_literal_does_nothing_if_the_clause_is_already_sat_2(){
        let mut dummy= Dummy::new(8);

        dummy.set_value(lit(1), Bool::False);
        dummy.set_value(lit(2), Bool::True);
        dummy.set_value(lit(4), Bool::False);
        dummy.set_value(lit(8), Bool::Undef);

        // create the tested clause
        let mut clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        dummy.add_clause(clause);

        let watched = Literal::from(1);
        assert_eq!(dummy.find_new_literal(0, watched), Ok(Literal::from(1)))
    }

    #[test]
    fn find_new_literal_returns_ok_with_the_first_unassigned(){
        let mut dummy= Dummy::new(8);

        dummy.set_value(lit(1), Bool::False);
        dummy.set_value(lit(2), Bool::False);
        dummy.set_value(lit(4), Bool::Undef);
        dummy.set_value(lit(8), Bool::Undef);

        // create the tested clause
        let mut clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        dummy.add_clause(clause);

        let watched = Literal::from(1);
        assert_eq!(dummy.find_new_literal(0, watched), Ok(Literal::from(4)))
    }

    #[test]
    fn find_new_literal_does_not_pick_one_of_the_wl_as_new_wl(){
        let mut dummy= Dummy::new(8);

        dummy.set_value(lit(1), Bool::False);
        dummy.set_value(lit(2), Bool::Undef);
        dummy.set_value(lit(4), Bool::False);
        dummy.set_value(lit(8), Bool::Undef);

        // create the tested clause
        let mut clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        dummy.add_clause(clause);

        let watched = Literal::from(1);
        assert_eq!(dummy.find_new_literal(0, watched), Ok(Literal::from(8)))
    }

    #[test]
    fn find_new_literal_returns_ok_with_first_satisfied_literal_when_one_is_found_1(){
        let mut dummy= Dummy::new(8);

        dummy.set_value(lit(1), Bool::False);
        dummy.set_value(lit(2), Bool::Undef);
        dummy.set_value(lit(4), Bool::True);
        dummy.set_value(lit(8), Bool::Undef);

        // create the tested clause
        let mut clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        dummy.add_clause(clause);

        let watched = Literal::from(1);
        assert_eq!(dummy.find_new_literal(0, watched), Ok(Literal::from(4)))
    }

    #[test]
    fn find_new_literal_returns_ok_with_first_satisfied_literal_when_one_is_found_2(){
        let mut dummy= Dummy::new(8);

        dummy.set_value(lit(1), Bool::False);
        dummy.set_value(lit(2), Bool::Undef);
        dummy.set_value(lit(4), Bool::False);
        dummy.set_value(lit(8), Bool::True);

        // create the tested clause
        let mut clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        dummy.add_clause(clause);

        let watched = Literal::from(1);
        assert_eq!(dummy.find_new_literal(0, watched), Ok(Literal::from(8)))
    }

    #[test]
    fn find_new_literal_tells_what_literal_to_assert_when_it_fails_to_find_a_new_lit(){
        let mut dummy= Dummy::new(8);

        dummy.set_value(lit(1), Bool::False);
        dummy.set_value(lit(2), Bool::Undef);
        dummy.set_value(lit(4), Bool::False);
        dummy.set_value(lit(8), Bool::False);

        // create the tested clause
        let mut clause = Clause::new(vec![
            Literal::from(1),
            Literal::from(2),
            Literal::from(4),
            Literal::from(8)], false);

        dummy.add_clause(clause);

        let watched = Literal::from(1);
        assert_eq!(dummy.find_new_literal(0, watched), Err(Literal::from(2)))
    }

    #[test]
    #[should_panic]
    fn activate_must_fail_for_empty_clause() {
        let mut dummy= Dummy::new(8);
        dummy.add_clause(Clause::new(vec![], false));

        dummy.activate_clause(0);
    }

    #[test]
    #[should_panic]
    fn activate_must_fail_for_unary_clause() {
        let mut dummy= Dummy::new(8);
        dummy.add_clause(Clause::new(vec![lit(-1)], false));

        dummy.activate_clause(0);
    }

    #[test]
    fn activate_should_tell_if_it_failed_to_find_any_literal_to_watch() {
        let mut dummy= Dummy::new(8);
        dummy.set_value(lit(-1), Bool::False);
        dummy.set_value(lit(-2), Bool::False);

        let clause = Clause::new(vec![lit(-1), lit(-2)], false);
        dummy.add_clause(clause);

        assert_eq!(ActivationStatus::ConflictDetected, dummy.activate_clause(0));
    }

    #[test]
    fn activate_should_not_add_watches_if_wl_cant_be_found() {
        let mut dummy= Dummy::new(8);
        dummy.set_value(lit(-1), Bool::False);
        dummy.set_value(lit(-2), Bool::False);

        let clause = Clause::new(vec![lit(-1), lit(-2)], false);
        dummy.add_clause(clause);

        assert_eq!(dummy.get_watchers(lit(-1)), &[ ]);
        assert_eq!(dummy.get_watchers(lit(-2)), &[ ]);

        dummy.activate_clause(0);

        assert_eq!(dummy.get_watchers(lit(-1)), &[ ]);
        assert_eq!(dummy.get_watchers(lit(-2)), &[ ]);
    }

    #[test]
    fn activate_should_tell_if_it_could_only_find_one_literal_to_watch_wl_is_true() {
        let mut dummy= Dummy::new(8);
        dummy.set_value(lit(-1), Bool::False);
        dummy.set_value(lit(-2), Bool::True);

        let clause = Clause::new(vec![lit(-1), lit(-2)], false);
        dummy.add_clause(clause);

        assert_eq!(ActivationStatus::UnitDetected(lit(-2)), dummy.activate_clause(0));
    }

    #[test]
    fn activate_should_tell_if_it_could_only_find_one_literal_to_watch_wl_is_undef() {
        let mut dummy= Dummy::new(8);
        dummy.set_value(lit(-1), Bool::False);
        dummy.set_value(lit(-2), Bool::Undef);

        let clause = Clause::new(vec![lit(-1), lit(-2)], false);
        dummy.add_clause(clause);

        assert_eq!(ActivationStatus::UnitDetected(lit(-2)), dummy.activate_clause(0));
    }

    #[test]
    fn activate_should_add_two_watchers_even_if_it_could_only_find_one_literal_to_watch() {
        let mut dummy= Dummy::new(8);
        dummy.set_value(lit(-1), Bool::False);
        dummy.set_value(lit(-2), Bool::True);

        let clause = Clause::new(vec![lit(-1), lit(-2)], false);
        dummy.add_clause(clause);

        assert_eq!(dummy.get_watchers(lit(-1)), &[ ]);
        assert_eq!(dummy.get_watchers(lit(-2)), &[ ]);

        dummy.activate_clause(0);

        assert_eq!(dummy.get_watchers(lit(-1)), &[0]);
        assert_eq!(dummy.get_watchers(lit(-2)), &[0]);
    }

    #[test]
    fn activate_should_tell_if_two_wl_could_be_found_both_undef() {
        let mut dummy= Dummy::new(8);
        dummy.set_value(lit(-1), Bool::Undef);
        dummy.set_value(lit(-2), Bool::Undef);

        let clause = Clause::new(vec![lit(-1), lit(-2)], false);
        dummy.add_clause(clause);

        assert_eq!(ActivationStatus::FoundTwoWatchers, dummy.activate_clause(0));
    }
    #[test]
    fn activate_should_tell_if_two_wl_could_be_found_both_true() {
        let mut dummy= Dummy::new(8);
        dummy.set_value(lit(-1), Bool::Undef);
        dummy.set_value(lit(-2), Bool::Undef);

        let clause = Clause::new(vec![lit(-1), lit(-2)], false);
        dummy.add_clause(clause);

        assert_eq!(ActivationStatus::FoundTwoWatchers, dummy.activate_clause(0));
    }
    #[test]
    fn activate_should_tell_if_two_wl_could_be_found_both_one_undef_one_true() {
        let mut dummy= Dummy::new(8);
        dummy.set_value(lit(-1), Bool::True);
        dummy.set_value(lit(-2), Bool::Undef);

        let clause = Clause::new(vec![lit(-1), lit(-2)], false);
        dummy.add_clause(clause);

        assert_eq!(ActivationStatus::FoundTwoWatchers, dummy.activate_clause(0));
    }
    #[test]
    fn activate_should_add_two_watchers() {
        let mut dummy= Dummy::new(8);
        dummy.set_value(lit(-1), Bool::True);
        dummy.set_value(lit(-2), Bool::True);

        let clause = Clause::new(vec![lit(-1), lit(-2)], false);
        dummy.add_clause(clause);

        assert_eq!(dummy.get_watchers(lit(-1)), &[ ]);
        assert_eq!(dummy.get_watchers(lit(-2)), &[ ]);

        dummy.activate_clause(0);

        assert_eq!(dummy.get_watchers(lit(-1)), &[0]);
        assert_eq!(dummy.get_watchers(lit(-2)), &[0]);
    }

    #[test]
    #[should_panic]
    // This should never happen in practice
    fn deactivate_should_fail_for_empty_clause() {
        let mut dummy= Dummy::new(8);
        dummy.set_value(lit(-1), Bool::True);
        dummy.set_value(lit(-2), Bool::True);

        let clause = Clause::new(vec![lit(-1), lit(-2)], false);
        dummy.add_clause(clause);

        dummy.get_clause_mut(0).clear();
        dummy.deactivate_clause(0);
    }
    #[test]
    #[should_panic]
    // This should never happen in practice
    fn deactivate_should_fail_for_unary_clause() {
        let mut dummy= Dummy::new(8);
        dummy.set_value(lit(-1), Bool::True);
        dummy.set_value(lit(-2), Bool::True);

        let clause = Clause::new(vec![lit(-1), lit(-2)], false);
        dummy.add_clause(clause);

        dummy.get_clause_mut(0).clear();
        dummy.get_clause_mut(0).push(lit(-1));
        dummy.deactivate_clause(0);
    }

    #[test]
    fn deactivate_should_remove_all_watchers() {
        let mut dummy= Dummy::new(8);
        dummy.set_value(lit(-1), Bool::True);
        dummy.set_value(lit(-2), Bool::True);

        let clause = Clause::new(vec![lit(-1), lit(-2)], false);
        dummy.add_clause(clause);
        dummy.activate_clause(0);

        assert_eq!(dummy.get_watchers(lit(-1)), &[0]);
        assert_eq!(dummy.get_watchers(lit(-2)), &[0]);

        dummy.deactivate_clause(0);
        
        assert_eq!(dummy.get_watchers(lit(-1)), &[ ]);
        assert_eq!(dummy.get_watchers(lit(-2)), &[ ]);
    }
}