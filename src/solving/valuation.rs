use core::*;
use collections::*;

// -----------------------------------------------------------------------------------------------
/// # Valuation
/// This trait encapsulates the idea of an assignment of Variables to Bool values.
// -----------------------------------------------------------------------------------------------
pub trait Valuation {

    /// Provides a reference to the underlying data storage
    fn get_valuation_data    (&    self) -> &    VarIdxVec<Bool>;

    /// Provides a mutable reference to the underlying data storage
    fn get_valuation_data_mut(&mut self) -> &mut VarIdxVec<Bool>;

    /// Tells the truth value of the given literal `l` in the current assignment
    fn get_value(&self, l: Literal) -> Bool {
        let value = self.get_valuation_data()[l.var()];

        match l.sign() {
            Sign::Positive =>  value,
            Sign::Negative => !value
        }
    }

    /// Sets the truth value of the given literal `l` in the current assignment
    fn set_value(&mut self, l: Literal, value : Bool) {
        self.get_valuation_data_mut()[l.var()] = match l.sign() {
            Sign::Positive =>  value,
            Sign::Negative => !value
        }
    }

    /// Tells whether `l` wasn't assigned any value yet.
    fn is_undef(&self, l: Literal) -> bool { self.get_value(l) == Bool::Undef }

    /// Tells whether `l` was set to True
    fn is_true (&self, l: Literal) -> bool { self.get_value(l) == Bool::True  }

    /// Tells whether `l` was set to False
    fn is_false(&self, l: Literal) -> bool { self.get_value(l) == Bool::False }

    /// Tells number of variables in the problem
    fn nb_vars(&self) -> usize { self.get_valuation_data().len() }
}

// Implementation in trivial: No unit tests provided.