#[allow(non_camel_case_types)]
pub type uint = u32;
#[allow(non_camel_case_types)]
pub type iint = i32;

mod bool;
mod variable;
mod sign;
mod literal;
mod clause;
mod valuation;

// re-export all types
pub use self::bool::Bool;
pub use self::variable::Variable;
pub use self::sign::Sign;
pub use self::literal::Literal;
pub use self::clause::Clause;
pub use self::valuation::Valuation;

/// A shortcut notation to make a literal out of a number value
pub fn lit(l: iint) -> Literal  { Literal::from(l) }

/// A shortcut notation to make a variable out of a number value
pub fn var(v: uint) -> Variable { Variable::from(v) }