use std::usize;

pub type ClauseId = usize;

pub type Watcher  = ClauseId;
pub type Conflict = ClauseId;
pub type Reason   = ClauseId;

pub const CLAUSE_ELIDED: ClauseId = usize::MAX;

mod clause_database;
pub use self::clause_database::*;

mod valuation;
pub use self::valuation::*;

mod watched_literals;
pub use self::watched_literals::*;

mod variable_selection;
mod restart_strategy;
mod flags;
mod solver;

pub use self::variable_selection::*;
pub use self::restart_strategy::*;

pub use self::flags::{Flag, Flags};
pub use self::solver::Solver;