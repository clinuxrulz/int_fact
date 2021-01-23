use std::collections::HashMap;
use crate::{CnfClause, CnfFormula, Lit, Var};

pub struct DensityCtx {
    cnf: CnfFormula,
    cache: HashMap<CnfFormula,f64>,
}

impl DensityCtx {
    pub fn new<Cnf:Into<CnfFormula>>(cnf: Cnf) -> DensityCtx {
        let mut cnf: CnfFormula = cnf.into();
        for clause in &mut cnf {
            clause.simplify();
        }
        DensityCtx {
            cnf: cnf.into(),
            cache: HashMap::new()
        }
    }

    pub fn solve(&mut self) -> f64 {
        self.cnf_density(self.cnf.clone(), 0)
    }

    pub fn cnf_density(&mut self, cnf: CnfFormula, lvl: usize) -> f64 {
        if cnf.is_empty() {
            return 1.0;
        }
        if cnf.len() == 1 && cnf[0].is_empty() {
            return 0.0;
        }
        if let Some(d) = self.cache.get(&cnf) {
            return *d;
        }
        // d(f(a+b)) = d(f) - d(f|!a!b)d(!a!b)
        let mut f = 1.0_f64;
        let mut cnf2 = CnfFormula::new();
        let mut idx: usize = 0;
        if self.cache.len() > 1000 {
            self.cache.clear();
        }
        for clause in &cnf {
            idx += 1;
            if lvl == 0 {
                println!("{:?}", clause);
                println!("{}/{}", idx, cnf.len());
                println!("{}", self.cache.len());
                println!("d(f) = {}", f);
            }
            let mut cnf3 = cnf2.clone();
            cnf2.push(clause.clone());
            for lit in clause {
                cnf3.assign_lit(lit.negated());
            }
            f -= self.cnf_density(cnf3,lvl+1) * 2.0_f64.powf(-(clause.len() as f64));
        }
        self.cache.insert(cnf, f);
        f
    }
}

#[test]
fn test_density() {
    let cnf = CnfFormula::from(vec![vec![1,-2],vec![-1,2]]);
    let mut density_ctx = DensityCtx::new(cnf);
    println!("{}", density_ctx.solve());
}

