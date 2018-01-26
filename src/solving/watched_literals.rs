use core::*;
use collections::*;

use super::*;

#[must_use]
#[derive(Debug)]
pub enum ActivationStatus {
    FoundTwoWatchers,
    UnitDetected(Literal),
    ConflictDetected
}

pub trait WatchedLiterals : ClauseDatabase + Valuation {
    fn get_watchers_list    (&self)     -> &    LitIdxVec<Vec<Watcher>>;
    fn get_watchers_list_mut(&mut self) -> &mut LitIdxVec<Vec<Watcher>>;

    #[inline]
    fn get_watchers(&self, lit: Literal) -> &[Watcher] {
        &self.get_watchers_list()[lit]
    }
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


    /// Activate the given clause.
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

    /// Deactivate the given clause.
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