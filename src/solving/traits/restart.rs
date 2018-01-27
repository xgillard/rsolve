// -----------------------------------------------------------------------------------------------
/// # Restart
/// This trait specifies the public interface of a solver cabable of restarting its search.
// -----------------------------------------------------------------------------------------------
pub trait Restart {
    /// Tells if the current search shoudl be aborted and be replaced by a complete restart.
    fn should_restart(&self) -> bool;

    /// Restarts the search to find a better path towards the solution.
    fn restart(&mut self);
}