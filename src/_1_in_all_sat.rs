use crate::_3Sat;
use std::collections::HashSet;
use std::fmt;

// Frank Vega. ONE-IN-THREE 3SAT is in P. 2014. hal-01069057

pub struct _1InAllSat {
    pub clauses: Vec<Vec<isize>>,
}

impl _1InAllSat {
    pub fn from_clauses(clauses: Vec<Vec<isize>>) -> _1InAllSat {
        _1InAllSat { clauses }
    }

    pub fn from_3sat(sat: &_3Sat) -> _1InAllSat {
        let mut next_var = 1;
        for clause in &sat.clauses {
            for lit in clause {
                let var = lit.abs();
                if var >= next_var {
                    next_var = var + 1;
                }
            }
        }
        let mut result: Vec<Vec<isize>> = Vec::new();
        for &[ref x, ref y, ref z] in &sat.clauses {
            let x = *x;
            let y = *y;
            let z = *z;
            let a = next_var;
            let b = next_var + 1;
            let c = next_var + 2;
            let d = next_var + 3;
            next_var += 4;
            result.push(vec![-x, a, b]);
            result.push(vec![b, y, c]);
            result.push(vec![c, d, -z]);
        }
        _1InAllSat { clauses: result }
    }

    pub fn solve(&mut self) -> Option<HashSet<isize>> {
        let mut solution: HashSet<isize> = HashSet::new();
        loop {
            loop {
                let changed = self.depuration(&mut solution);
                if self.clauses.is_empty() {
                    return Some(solution);
                } else if self.clauses.iter().any(|c| c.is_empty()) {
                    return None;
                }
                if !changed {
                    break;
                }
            }
            let changed = self.matching();
            if !changed {
                return Some(solution);
            }
        }
    }

    fn depuration(&mut self, solution: &mut HashSet<isize>) -> bool {
        self.apply_lemma_3_1(solution)
            || self.apply_lemma_3_2(solution)
            || self.apply_lemma_3_3(solution)
            || self.apply_lemma_3_4(solution)
    }

    fn matching(&mut self) -> bool {
        self.apply_lemma_3_8()
    }

    fn apply_lemma_3_1(&mut self, solution: &mut HashSet<isize>) -> bool {
        let mut changed = false;
        let mut new_solutions: HashSet<isize> = HashSet::new();
        for i in 0..self.clauses.len() - 1 {
            for j in (i + 1)..self.clauses.len() {
                let mut alt_lit_op: Option<isize> = None;
                {
                    let clause_i = &self.clauses[i];
                    let clause_j = &self.clauses[j];
                    'outer: for lit1 in clause_i {
                        for lit2 in clause_j {
                            if *lit2 == -*lit1 {
                                alt_lit_op = Some(lit1.abs());
                                break 'outer;
                            }
                        }
                    }
                }
                if let Some(alt_lit) = alt_lit_op {
                    let lits1: HashSet<isize> = self.clauses[i]
                        .iter()
                        .filter(|lit| lit.abs() != alt_lit)
                        .map(|x| *x)
                        .collect();
                    let lits2: HashSet<isize> = self.clauses[j]
                        .iter()
                        .filter(|lit| lit.abs() != alt_lit)
                        .map(|x| *x)
                        .collect();
                    let mut lits: HashSet<isize> = HashSet::new();
                    for lit in &lits1 {
                        if lits2.contains(lit) {
                            lits.insert(*lit);
                        }
                    }
                    for lit in &lits2 {
                        if lits1.contains(lit) {
                            lits.insert(*lit);
                        }
                    }
                    for lit in &lits {
                        solution.insert(-*lit);
                        new_solutions.insert(-*lit);
                    }
                    let i_len = self.clauses[i].len();
                    let j_len = self.clauses[j].len();
                    self.clauses[i].retain(|lit| !lits.contains(lit));
                    self.clauses[j].retain(|lit| !lits.contains(lit));
                    changed |= self.clauses[i].len() != i_len;
                    changed |= self.clauses[j].len() != j_len;
                }
            }
        }
        for i in (0..self.clauses.len()).rev() {
            let found = self.clauses[i]
                .iter()
                .any(|lit| new_solutions.contains(lit));
            if found {
                self.clauses.remove(i);
            }
        }
        if changed {
            println!("lemma 3.1: {}", self);
        }
        changed
    }

    fn apply_lemma_3_2(&mut self, solution: &mut HashSet<isize>) -> bool {
        let mut changed = false;
        for i in (0..self.clauses.len()).rev() {
            if self.clauses[i].len() == 1 {
                let lit = self.clauses[i][0].abs();
                let mut found = false;
                'outer: for j in 0..self.clauses.len() {
                    if j == i {
                        continue;
                    }
                    for lit2 in &self.clauses[j] {
                        if lit2.abs() == lit {
                            found = true;
                            break 'outer;
                        }
                    }
                }
                if !found {
                    solution.insert(self.clauses[i][0]);
                    self.clauses.remove(i);
                    changed = true;
                }
            }
        }
        if changed {
            println!("lemma 3.2: {}", self);
        }
        changed
    }

    fn apply_lemma_3_3(&mut self, solution: &mut HashSet<isize>) -> bool {
        let mut changed = false;
        let mut single_lits: HashSet<isize> = HashSet::new();
        for clause in &self.clauses {
            if clause.len() == 1 {
                single_lits.insert(clause[0]);
                solution.insert(clause[0]);
            }
        }
        for i in (0..self.clauses.len()).rev() {
            let found = self.clauses[i].iter().any(|x| single_lits.contains(x));
            if self.clauses[i].len() > 1 && found {
                self.clauses.remove(i);
                changed = true;
            }
        }
        if changed {
            println!("lemma 3.3: {}", self);
        }
        changed
    }

    fn apply_lemma_3_4(&mut self, solution: &mut HashSet<isize>) -> bool {
        let mut changed = false;
        let mut false_lits: HashSet<isize> = HashSet::new();
        for i in (0..self.clauses.len()).rev() {
            let clause = &self.clauses[i];
            if clause.is_empty() {
                continue;
            }
            let mut alt_lit_op: Option<isize> = None;
            'outer: for i in 0..clause.len() - 1 {
                let lit1 = clause[i];
                for j in (i + 1)..clause.len() {
                    let lit2 = clause[j];
                    if lit2 == -lit1 {
                        alt_lit_op = Some(lit1.abs());
                        break 'outer;
                    }
                }
            }
            if let Some(alt_lit) = alt_lit_op {
                for lit in clause {
                    if lit.abs() == alt_lit {
                        continue;
                    }
                    false_lits.insert(*lit);
                    changed = true;
                }
            }
            std::mem::drop(clause);
            if alt_lit_op.is_some() {
                self.clauses.remove(i);
            }
        }
        for clause in &mut self.clauses {
            clause.retain(|lit| !false_lits.contains(lit));
        }
        for i in (0..self.clauses.len()).rev() {
            let found = self.clauses[i].iter().any(|lit| false_lits.contains(&-lit));
            if found {
                self.clauses.remove(i);
            }
        }
        for lit in false_lits {
            solution.insert(-lit);
        }
        if changed {
            println!("lemma 3.4: {}", self);
        }
        changed
    }

    fn apply_lemma_3_5(&mut self) -> bool {
        unimplemented!();
    }

    fn apply_lemma_3_8(&mut self) -> bool {
        let mut changed = false;
        loop {
            let mut again = false;
            'outer: for i in 0..self.clauses.len() - 1 {
                for j in (i + 1)..self.clauses.len() {
                    let mut alt_lit_op: Option<isize> = None;
                    {
                        let clause_i = &self.clauses[i];
                        let clause_j = &self.clauses[j];
                        'outer2: for lit1 in clause_i {
                            for lit2 in clause_j {
                                if *lit2 == -*lit1 {
                                    alt_lit_op = Some(*lit1);
                                    break 'outer2;
                                }
                            }
                        }
                    }
                    if let Some(alt_lit) = alt_lit_op {
                        let mut c2 = self.clauses.remove(j);
                        let mut c1 = self.clauses.remove(i);
                        for k in 0..c1.len() {
                            if c1[k] == alt_lit {
                                c1.remove(k);
                                break;
                            }
                        }
                        for k in 0..c2.len() {
                            if c2[k] == -alt_lit {
                                c2.remove(k);
                                break;
                            }
                        }
                        c1.append(&mut c2);
                        self.clauses.push(c1);
                        changed = true;
                        again = true;
                        break 'outer;
                    }
                }
            }
            if !again {
                break;
            }
        }
        if changed {
            println!("lemma 3.8: {}", self);
        }
        changed
    }
}

impl fmt::Display for _1InAllSat {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first_and = true;
        for clause in &self.clauses {
            if first_and {
                first_and = false;
            } else {
                write!(formatter, ",")?;
            }
            let mut first_or = true;
            write!(formatter, "{{")?;
            for lit in clause {
                if first_or {
                    first_or = false;
                } else {
                    write!(formatter, ",")?;
                }
                write!(formatter, "{}", lit)?;
            }
            write!(formatter, "}}")?;
        }
        Ok(())
    }
}

#[test]
fn test_1_in_all_sat() {
    let mut sat = _1InAllSat::from_clauses(vec![vec![1, -1, -2], vec![3, 2, 4], vec![-1, -3, -4]]);
    println!("{}", sat);
    println!();
    println!("{:?}", sat.solve());
}
