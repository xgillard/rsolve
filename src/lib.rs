//! The variables and literals are implemented as plain integers
pub type Variable = u32;
pub type Literal  = i32;

pub mod arrays;
pub mod branching;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
    }
}
