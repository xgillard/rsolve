use std::usize;
use core::*;
use collections::*;

pub type ClauseId = usize;

pub type Watcher  = ClauseId;
pub type Conflict = ClauseId;
pub type Reason   = ClauseId;

pub const CLAUSE_ELIDED: ClauseId = usize::MAX;


pub trait ClauseDatabase {
    fn get_clauses    (&self)     -> &    [Clause];
    fn get_clauses_mut(&mut self) -> &mut [Clause];

    fn get_clause    (&self,     c_id: ClauseId) -> &Clause     { &    self.get_clauses    ()[c_id]}
    fn get_clause_mut(&mut self, c_id: ClauseId) -> &mut Clause { &mut self.get_clauses_mut()[c_id]}
}

pub trait Valuation {
    fn get_valuation_data    (&    self) -> &    VarIdxVec<Bool>;
    fn get_valuation_data_mut(&mut self) -> &mut VarIdxVec<Bool>;

    fn get_value(&self, l: Literal) -> Bool {
        let value = self.get_valuation_data()[l.var()];

        match l.sign() {
            Sign::Positive =>  value,
            Sign::Negative => !value
        }
    }

    fn set_value(&mut self, l: Literal, value : Bool) {
        self.get_valuation_data_mut()[l.var()] = match l.sign() {
            Sign::Positive =>  value,
            Sign::Negative => !value
        }
    }

    fn is_undef(&self, l: Literal) -> bool { self.get_value(l) == Bool::Undef }

    fn is_true (&self, l: Literal) -> bool { self.get_value(l) == Bool::True  }

    fn is_false(&self, l: Literal) -> bool { self.get_value(l) == Bool::False }

    fn nb_vars(&self) -> usize { self.get_valuation_data().len() }
}

pub trait WatchedLiterals : ClauseDatabase + Valuation {
    fn get_watchers    (&self)     -> &    [Vec<Watcher>];
    fn get_watchers_mut(&mut self) -> &mut [Vec<Watcher>];

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
}

/*

    fn get_watchers    (&self)     -> &    [Vec<Watcher>];
    fn get_watchers_mut(&mut self) -> &mut [Vec<Watcher>];

    /// Activate the given clause.
    /// It is assumed that clauses of size 0 and 1 are out of the way and we're certain to be left
    /// only with clauses having at least two literals.
    fn activate_clause(&mut self, c_id : ClauseId) -> Result<ClauseId, ()> {
        let mut cnt = 0;

        let mut wl1 = self.get_clause(c_id)[0];
        let mut pl1 = 0;

        let mut wl2 = self.get_clause(c_id)[1];
        let mut pl2 = 1;

        {
            let mut watchables = self.get_clause(c_id).iter()
                .enumerate()
                .filter(|&(_, &l)| !self.valuation.is_false(l));

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
            return Err(());
        }
        // the clause is unit (under assignment) so we need to assert wl1.
        // this is going to work since we know that wl1 is watchable
        if cnt == 1 {
            self.assign(wl1, Some(c_id)).unwrap();
        }

        // anyhow, remember that we must watch wl1 and wl2
        self.clauses[c_id].swap(0, pl1);
        self.clauses[c_id].swap(1, pl2);

        self.watchers[wl1].push(c_id);
        self.watchers[wl2].push(c_id);

        return Ok(c_id);
    }
}
*/