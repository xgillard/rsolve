use core::*;
use collections::VarIdxVec;

// -----------------------------------------------------------------------------------------------
/// # Valuation
/// This struct encapsulates the idea of an assignment of Variables to Bool values.
// -----------------------------------------------------------------------------------------------

#[derive(Debug)]
pub struct Valuation ( VarIdxVec<Bool> );

impl Valuation {

    pub fn new(nb_vars: usize) -> Valuation {
        let mut valuation= Valuation(VarIdxVec::with_capacity(nb_vars));
        // initialize the items
        for _ in 0..nb_vars {
            valuation.0.push(Bool::Undef );
        }
        return valuation;
    }

    pub fn get_value(&self, l: Literal) -> Bool {
        let value = self.0[l.var()];

        match l.sign() {
            Sign::Positive =>  value,
            Sign::Negative => !value
        }
    }

    pub fn set_value(&mut self, l: Literal, value : Bool) {
        self.0[l.var()] = match l.sign() {
            Sign::Positive =>  value,
            Sign::Negative => !value
        }
    }

    pub fn is_undef(&self, l: Literal) -> bool {
        self.get_value(l) == Bool::Undef
    }

    pub fn is_true (&self, l: Literal) -> bool {
        self.get_value(l) == Bool::True
    }

    pub fn is_false(&self, l: Literal) -> bool {
        self.get_value(l) == Bool::False
    }

    pub fn nb_vars(&self) -> usize { self.0.len() }
}