/// Abstraction of a restart strategy.
pub trait RestartStrategy {
    /// Tells whether the solver should restart given it has already encountered `nb_conflicts`
    fn is_restart_required(&self, nb_conflict: usize) -> bool;

    /// Sets the next conflict limit before the next restart
    fn set_next_limit(&mut self);
}

mod luby;
pub use self::luby::Luby;