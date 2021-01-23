use wasm_bindgen::prelude::*;

mod dimacs;
pub mod heuristic;
mod random;
mod sat;

pub use crate::dimacs::parse_dimacs;
pub use crate::random::{Rand, Rng};
pub use crate::sat::Sat;

#[wasm_bindgen]
pub fn solve(cnf: &str) -> String {
    let sat_op = parse_dimacs(cnf);
    if sat_op.is_none() {
        return "Parsing failed!".into();
    }
    let sat = sat_op.unwrap();
    format!("{:?}", sat.solve())
}
