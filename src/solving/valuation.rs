use core::*;
use collections::*;

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