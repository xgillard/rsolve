use core::*;
use super::*;

// -----------------------------------------------------------------------------------------------
/// # Propagation
/// This trait communicates the intent that object implementing this trait will perform some
/// propagation in order to carry out inference.
// -----------------------------------------------------------------------------------------------
pub trait Propagation {
    /// Assigns a given literal to True. That is to say, it assigns a value to the given literal
    /// and it enqueues the negation of the literal on the propagation queue.
    ///
    /// The optional reason is specified whenever the assignment follows from all the other literals
    /// in the clause (the reason) being falsified.
    ///
    /// # Note
    /// We always push the *negation* of the assigned literal on the stack
    fn assign(&mut self, lit: Literal, reason: Option<Reason>) -> Result<(), ()>;

    /// This method propagates the information about all the literals that have been
	/// enqueued. It returns an optional conflicting clause whenever conflict is detected
	/// Otherwise, None is returned.
    fn propagate(&mut self) -> Option<Conflict>;
}