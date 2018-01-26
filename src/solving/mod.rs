use std::usize;

pub type ClauseId = usize;

pub type Watcher  = ClauseId;
pub type Conflict = ClauseId;
pub type Reason   = ClauseId;

pub const CLAUSE_ELIDED: ClauseId = usize::MAX;

mod traits;
pub use self::traits::*;

mod variable_selection;
mod restart_strategy;
mod flags;
mod solver;

pub use self::variable_selection::*;
pub use self::restart_strategy::*;

pub use self::flags::{Flag, Flags};
pub use self::solver::Solver;