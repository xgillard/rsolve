use super::RestartStrategy;

/// This structure encapsulates the restart strategy of the solver.
/// It is implemented using D.Knuth's 'reluctant doubling' algorithm
/// to generate luby sequence in $$\theta(1)$$ [time and space]
#[derive(Debug)]
pub struct Luby {
    /// the tuple from the reluctant doubling algorithm
    u : isize,
    v : isize,

    /// the length of an unit run
    unit  : usize,
    /// conflict limit = 2^shift * unit
    shift : usize
}

impl RestartStrategy for Luby {
    /// Tells whether the solver should restart given it has already encountered `nb_conflicts`
    #[inline]
    fn is_restart_required(&self, nb_conflict: usize) -> bool {
        nb_conflict > (self.unit << self.shift)
    }

    /// Sets the next conflict limit before the next restart
    #[inline]
    fn set_next_limit(&mut self) {
        self.shift = self.luby();
    }
}

impl Luby {
    /// Creates a new instance having the given unit run
    pub fn new(unit: usize) -> Luby {
        Luby {
            u: 1,
            v: 1,
            shift: 0,
            unit
        }
    }

    /// This is the core of the strategy where D. Knuth's reluctant doubling algorithm
    /// is implemented to generate a luby sequence.
    #[inline]
    fn luby(&mut self) -> usize {
        let res = self.v;

        if self.u & -self.u == self.v {
            self.u += 1;
            self.v  = 1;
        } else {
            self.v *= 2;
        }

        return res as usize;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn luby_generates_luby_sequence() {
        let mut tested = Luby::new(100);

        assert_eq!(tested.luby(), 1);
        assert_eq!(tested.luby(), 1);
        assert_eq!(tested.luby(), 2);
        assert_eq!(tested.luby(), 1);
        assert_eq!(tested.luby(), 1);
        assert_eq!(tested.luby(), 2);
        assert_eq!(tested.luby(), 4);
        assert_eq!(tested.luby(), 1);
        assert_eq!(tested.luby(), 1);
        assert_eq!(tested.luby(), 2);
        assert_eq!(tested.luby(), 1);
        assert_eq!(tested.luby(), 1);
        assert_eq!(tested.luby(), 2);
        assert_eq!(tested.luby(), 4);
        assert_eq!(tested.luby(), 8);
    }

    #[test]
    fn is_restart_needed_follows_luby_sequence(){
        let mut tested = Luby::new(100);

        // 0
        assert_eq!(tested.is_restart_required(  1), false);
        assert_eq!(tested.is_restart_required( 10), false);
        assert_eq!(tested.is_restart_required( 99), false);
        assert_eq!(tested.is_restart_required(100), false);
        assert_eq!(tested.is_restart_required(101), true);

        // 1
        tested.set_next_limit();

        assert_eq!(tested.is_restart_required(  1), false);
        assert_eq!(tested.is_restart_required( 10), false);
        assert_eq!(tested.is_restart_required( 99), false);
        assert_eq!(tested.is_restart_required(100), false);
        assert_eq!(tested.is_restart_required(200), false);
        assert_eq!(tested.is_restart_required(201), true);

        // 1
        tested.set_next_limit();

        assert_eq!(tested.is_restart_required(  1), false);
        assert_eq!(tested.is_restart_required( 10), false);
        assert_eq!(tested.is_restart_required( 99), false);
        assert_eq!(tested.is_restart_required(100), false);
        assert_eq!(tested.is_restart_required(200), false);
        assert_eq!(tested.is_restart_required(201), true);

        // 2
        tested.set_next_limit();

        assert_eq!(tested.is_restart_required(  1), false);
        assert_eq!(tested.is_restart_required( 10), false);
        assert_eq!(tested.is_restart_required( 99), false);
        assert_eq!(tested.is_restart_required(100), false);
        assert_eq!(tested.is_restart_required(200), false);
        assert_eq!(tested.is_restart_required(300), false);
        assert_eq!(tested.is_restart_required(400), false);
        assert_eq!(tested.is_restart_required(401), true);

        // 1
        tested.set_next_limit();

        assert_eq!(tested.is_restart_required(  1), false);
        assert_eq!(tested.is_restart_required( 10), false);
        assert_eq!(tested.is_restart_required( 99), false);
        assert_eq!(tested.is_restart_required(100), false);
        assert_eq!(tested.is_restart_required(200), false);
        assert_eq!(tested.is_restart_required(201), true);

        // 1
        tested.set_next_limit();

        assert_eq!(tested.is_restart_required(  1), false);
        assert_eq!(tested.is_restart_required( 10), false);
        assert_eq!(tested.is_restart_required( 99), false);
        assert_eq!(tested.is_restart_required(100), false);
        assert_eq!(tested.is_restart_required(200), false);
        assert_eq!(tested.is_restart_required(201), true);

        // 2
        tested.set_next_limit();

        assert_eq!(tested.is_restart_required(  1), false);
        assert_eq!(tested.is_restart_required( 10), false);
        assert_eq!(tested.is_restart_required( 99), false);
        assert_eq!(tested.is_restart_required(100), false);
        assert_eq!(tested.is_restart_required(200), false);
        assert_eq!(tested.is_restart_required(300), false);
        assert_eq!(tested.is_restart_required(400), false);
        assert_eq!(tested.is_restart_required(401), true);

        // 4
        tested.set_next_limit();

        assert_eq!(tested.is_restart_required(  1), false);
        assert_eq!(tested.is_restart_required( 10), false);
        assert_eq!(tested.is_restart_required( 99), false);
        assert_eq!(tested.is_restart_required(100), false);
        assert_eq!(tested.is_restart_required(200), false);
        assert_eq!(tested.is_restart_required(300), false);
        assert_eq!(tested.is_restart_required(400), false);
        assert_eq!(tested.is_restart_required(500), false);
        assert_eq!(tested.is_restart_required(600), false);
        assert_eq!(tested.is_restart_required(700), false);
        assert_eq!(tested.is_restart_required(800), false);
        assert_eq!(tested.is_restart_required(801), false);
    }
}