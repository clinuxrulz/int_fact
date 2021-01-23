pub struct Rng {
    seed: u32,
}

impl Rng {
    pub fn new() -> Rng {
        Rng { seed: 1337593424 }
    }

    pub fn gen(&mut self) -> u32 {
        let x = self.seed.wrapping_mul(1664525).wrapping_add(1013904223);
        self.seed = x;
        x
    }
}

pub trait Rand<Output> {
    fn rand(&mut self) -> Output;
}

impl Rand<f64> for Rng {
    fn rand(&mut self) -> f64 {
        (self.gen() as f64) / (u32::MAX as f64)
    }
}
