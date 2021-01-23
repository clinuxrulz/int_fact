use crate::Rand;
use crate::Sat;
use std::collections::HashMap;

pub fn guess_var(rand: &mut dyn Rand<f64>, sat: &Sat) -> isize {
    let mut var_map: HashMap<isize, f64> = HashMap::new();
    let mut last_var_map: HashMap<isize, f64> = HashMap::new();
    let mut lit_score: HashMap<isize, usize> = HashMap::new();
    fn and(x: f64, y: f64) -> f64 {
        x * y
    }
    fn or(x: f64, y: f64) -> f64 {
        x + y - x * y
    }
    fn not(x: f64) -> f64 {
        1.0f64 - x
    }
    let mut last_z_op: Option<f64> = None;
    for _it in 0..10 {
        let mut z = 1.0f64;
        for clause in &sat.clauses {
            let mut w = 0.0f64;
            for lit in clause {
                let var = lit.abs();
                let v;
                let found;
                if let Some(v2) = var_map.get(&var) {
                    v = if *lit < 0 { not(*v2) } else { *v2 };
                    found = true;
                } else {
                    v = rand.rand();
                    found = false;
                }
                if !found {
                    var_map.insert(var, v);
                }
                w = or(w, v);
            }
            z = and(z, w);
        }
        if let Some(last_z) = last_z_op {
            let up = z > last_z;
            for (var, val) in &var_map {
                let last_val = last_var_map.get(var).unwrap();
                let inc_true;
                if *val > *last_val {
                    inc_true = up;
                } else {
                    inc_true = !up;
                }
                let inc_lit;
                if inc_true {
                    inc_lit = *var;
                } else {
                    inc_lit = -*var;
                }
                let mut found = false;
                if let Some(c) = lit_score.get_mut(&inc_lit) {
                    *c += 1;
                    found = true;
                }
                if !found {
                    lit_score.insert(inc_lit, 1);
                }
            }
        }
        last_z_op = Some(z);
        for (var, val) in &var_map {
            last_var_map.insert(*var, *val);
        }
    }
    let mut best_lit = sat.clauses[0][0];
    let mut best_score: usize = 0;
    for (lit, score) in lit_score {
        if score > best_score {
            best_lit = lit;
            best_score = score;
        }
    }
    println!("best_lit: {}", best_lit);
    best_lit
}
