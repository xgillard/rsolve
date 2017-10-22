
pub mod utils;
pub mod core;
pub mod collections;

pub mod branching;
pub mod flags;
pub mod solver;

// re-export
pub use self::core::*;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
    }
}
