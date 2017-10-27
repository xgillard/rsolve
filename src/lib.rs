
pub mod utils;
pub mod core;
pub mod collections;

pub mod branching;
pub mod flags;
pub mod solver;

// re-export
pub use self::core::*;

/// A shortcut notation to make a literal out of a number value
pub fn lit(l: iint) -> Literal  { Literal::from(l) }

/// A shortcut notation to make a variable out of a number value
pub fn var(v: uint) -> Variable { Variable::from(v) }