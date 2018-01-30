use std::usize;

pub type ClauseId = usize;

pub type Watcher  = ClauseId;
pub type Conflict = ClauseId;
pub type Reason   = ClauseId;

pub const CLAUSE_ELIDED: ClauseId = usize::MAX;

mod heuristics;
mod flags;
mod solver;

pub use self::heuristics::*;

pub use self::flags::{Flag, Flags};
pub use self::solver::Solver;