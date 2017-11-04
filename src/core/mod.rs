#[allow(non_camel_case_types)]
pub type uint = u32;
#[allow(non_camel_case_types)]
pub type iint = i32;

pub mod bool;
pub mod variable;
pub mod sign;
pub mod literal;
pub mod clause;

pub mod valuation;

// re-export all types
pub use self::bool::*;
pub use self::variable::*;
pub use self::sign::*;
pub use self::literal::*;
pub use self::clause::*;
pub use self::valuation::*;

/// A shortcut notation to make a literal out of a number value
pub fn lit(l: iint) -> Literal  { Literal::from(l) }

/// A shortcut notation to make a variable out of a number value
pub fn var(v: uint) -> Variable { Variable::from(v) }