//! The variables and literals are implemented as plain integers
pub type Variable = usize;
pub type Literal  = isize;

pub mod branching;
pub mod flags;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
    }
}
