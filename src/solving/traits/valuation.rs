use core::*;

// -----------------------------------------------------------------------------------------------
/// # Valuation
/// This trait encapsulates the idea of an assignment of Variables to Bool values.
// -----------------------------------------------------------------------------------------------
pub trait Valuation {
    /// Tells the truth value of the given literal `l` in the current assignment
    fn get_value(&self, l: Literal) -> Bool;

    /// Sets the truth value of the given literal `l` in the current assignment
    fn set_value(&mut self, l: Literal, value : Bool);

    /// Tells whether `l` wasn't assigned any value yet.
    fn is_undef(&self, l: Literal) -> bool { self.get_value(l) == Bool::Undef }

    /// Tells whether `l` was set to True
    fn is_true (&self, l: Literal) -> bool { self.get_value(l) == Bool::True  }

    /// Tells whether `l` was set to False
    fn is_false(&self, l: Literal) -> bool { self.get_value(l) == Bool::False }

    /// Tells number of variables in the problem
    fn nb_vars(&self) -> usize;
}