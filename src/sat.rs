use crate::heuristic::guess_var;
use crate::Rng;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::io::Write;

#[derive(Clone, Debug)]
pub struct Sat {
    pub clauses: Vec<Vec<isize>>,
}

pub struct SatSimplifyResult {
    pub equivalent: Vec<(isize, isize)>,
    pub assigned: Vec<isize>,
}

impl Sat {
    pub fn from_clauses(clauses: Vec<Vec<isize>>) -> Sat {
        Sat { clauses }
    }

    pub fn solve(&self) -> Option<HashSet<isize>> {
        let mut result: HashSet<isize> = HashSet::new();
        let mut sat = self.clone();
        loop {
            let mut again = false;
            let result_op = sat.solve2();
            if let Some(result2) = result_op {
                for lit in result2 {
                    if !result.get(&lit).is_some() {
                        result.insert(lit);
                        sat.assign_lit(lit);
                        again = true;
                    }
                }
            } else {
                return None;
            }
            if !again {
                break;
            }
        }
        return Some(result);
    }

    fn solve2(&self) -> Option<HashSet<isize>> {
        let mut rng = Rng::new();
        struct Frame {
            sat: Sat,
            equivalent: HashMap<isize, isize>,
            assigned: HashSet<isize>,
        }
        let mut stack: Vec<Frame> = Vec::new();
        stack.push(Frame {
            sat: self.clone(),
            equivalent: HashMap::new(),
            assigned: HashSet::new(),
        });
        while let Some(Frame {
            mut sat,
            mut equivalent,
            mut assigned,
        }) = stack.pop()
        {
            let simplify = sat.simplify();
            for &(ref x, ref y) in &simplify.equivalent {
                equivalent.insert(*x, *y);
                equivalent.insert(*y, *x);
            }
            for lit in simplify.assigned {
                assigned.insert(lit);
                if let Some(lit2) = equivalent.get(&lit) {
                    assigned.insert(*lit2);
                }
                if let Some(lit2) = equivalent.get(&-lit) {
                    assigned.insert(-*lit2);
                }
            }
            if sat.clauses.is_empty() {
                return Some(assigned);
            }
            if sat.has_empty_clause() {
                continue;
            }
            let mut sat2 = sat.clone();
            let equivalent2 = equivalent.clone();
            let mut assigned2 = assigned.clone();
            let lit = guess_var(&mut rng, &sat);
            sat.assign_lit(lit);
            assigned.insert(lit);
            sat2.assign_lit(-lit);
            assigned2.insert(-lit);
            stack.push(Frame {
                sat,
                equivalent,
                assigned,
            });
            stack.push(Frame {
                sat: sat2,
                equivalent: equivalent2,
                assigned: assigned2,
            });
        }
        return None;
    }

    pub fn is_sat(&self) -> bool {
        self.solve().is_some()
    }

    pub fn has_empty_clause(&self) -> bool {
        self.clauses.iter().any(|clause| clause.is_empty())
    }

    pub fn assign_lit(&mut self, lit: isize) {
        for i in (0..self.clauses.len()).rev() {
            let found = self.clauses[i].iter().any(|lit2| *lit2 == lit);
            if found {
                self.clauses.remove(i);
            } else {
                self.clauses[i].retain(|lit2| *lit2 != -lit);
            }
        }
    }

    pub fn simplify(&mut self) -> SatSimplifyResult {
        let mut result = SatSimplifyResult {
            equivalent: Vec::new(),
            assigned: Vec::new(),
        };
        loop {
            let mut again = false;
            {
                let mut lits: HashSet<isize> = HashSet::new();
                for clause in &mut self.clauses {
                    clause.sort();
                    clause.dedup();
                    clause.sort_by(|a, b| a.abs().cmp(&b.abs()));
                    if clause.len() == 1 {
                        lits.insert(clause[0]);
                    }
                }
                if !lits.is_empty() {
                    again = true;
                }
                for lit in lits {
                    self.assign_lit(lit);
                    result.assigned.push(lit);
                }
            }
            {
                for i in (0..self.clauses.len()).rev() {
                    if self.clauses[i].len() > 1 {
                        let mut remove = false;
                        for j in 0..self.clauses[i].len() - 1 {
                            if self.clauses[i][j] == -self.clauses[i][j + 1] {
                                remove = true;
                                break;
                            }
                        }
                        if remove {
                            self.clauses.remove(i);
                            again = true;
                        }
                    }
                }
            }
            if !self.clauses.is_empty() {
                let mut assigns: HashSet<(isize, isize)> = HashSet::new();
                for i in 0..self.clauses.len() - 1 {
                    if self.clauses[i].len() == 2 {
                        let w = self.clauses[i][0];
                        let x = self.clauses[i][1];
                        for j in (i + 1)..self.clauses.len() {
                            if self.clauses[j].len() == 2 {
                                let y = self.clauses[j][0];
                                let z = self.clauses[j][1];
                                if (w == -y && x == -z) || (w == -z && x == -y) {
                                    assigns.insert((w, -x));
                                }
                            }
                        }
                    }
                }
                if !assigns.is_empty() {
                    again = true;
                }
                for (x, y) in assigns {
                    for clause in &mut self.clauses {
                        for lit in clause {
                            if *lit == x {
                                *lit = y;
                            } else if *lit == -x {
                                *lit = -y;
                            }
                        }
                    }
                    result.equivalent.push((x, y));
                }
            }
            if !self.clauses.is_empty() {
                let mut lits: HashSet<isize> = HashSet::new();
                for i in 0..self.clauses.len() - 1 {
                    if self.clauses[i].len() == 2 {
                        let w = self.clauses[i][0];
                        let x = self.clauses[i][1];
                        for j in (i + 1)..self.clauses.len() {
                            if self.clauses[j].len() == 2 {
                                let y = self.clauses[j][0];
                                let z = self.clauses[j][1];
                                if w == y && x == -z {
                                    lits.insert(w);
                                } else if w == -y && x == z {
                                    lits.insert(x);
                                }
                            }
                        }
                    }
                }
                if !lits.is_empty() {
                    again = true;
                }
                for lit in lits {
                    self.assign_lit(lit);
                    result.assigned.push(lit);
                }
            }
            // resolution
            // (a or b or c) and (!a or b or d) -> (b or c or d)
            if !self.clauses.is_empty() && false {
                let mut new_clauses: Vec<Vec<isize>> = Vec::new();
                for [i1, j1, k1] in vec![[0, 1, 2], [1, 2, 0], [2, 0, 1]] {
                    for clause in &self.clauses {
                        if clause.len() != 3 {
                            continue;
                        }
                        let w1 = clause[i1];
                        let x1 = clause[j1];
                        let y1 = clause[k1];
                        for clause2 in &self.clauses {
                            if clause2.len() != 3 {
                                continue;
                            }
                            for [i2, j2, k2] in vec![[0, 1, 2], [1, 2, 0], [2, 0, 1]] {
                                let w2 = -clause2[i2];
                                let x2 = clause2[j2];
                                let z2 = clause2[k2];
                                if w2 != w1 || x2 != x1 {
                                    continue;
                                }
                                let mut new_clause = vec![x1, y1, z2];
                                new_clause.sort();
                                new_clause.dedup();
                                new_clause.sort_by(|a, b| a.abs().cmp(&b.abs()));
                                if !new_clause.is_empty() {
                                    let mut skip = false;
                                    for i in 0..new_clause.len() - 1 {
                                        if new_clause[i] == -new_clause[i + 1] {
                                            skip = true;
                                            break;
                                        }
                                    }
                                    if skip {
                                        continue;
                                    }
                                }
                                let exists = self
                                    .clauses
                                    .iter()
                                    .chain(new_clauses.iter())
                                    .any(|c| *c == new_clause);
                                if !exists {
                                    println!("added {:?}", new_clause);
                                    new_clauses.push(new_clause);
                                }
                            }
                        }
                    }
                }
                self.clauses.append(&mut new_clauses);
            }
            // double resolution
            // (a or b or c) and (a or !b) and (a or !c)
            if !self.clauses.is_empty() && false {
                let mut lits: Vec<isize> = Vec::new();
                for [i1, j1, k1] in vec![[0, 1, 2], [1, 2, 0], [2, 0, 1]] {
                    for clause in &self.clauses {
                        if clause.len() != 3 {
                            continue;
                        }
                        let x1 = clause[i1];
                        let y1 = clause[j1];
                        let z1 = clause[k1];
                        if y1 == z1 {
                            continue;
                        }
                        for [i2, j2] in vec![[0, 1], [1, 0]] {
                            for clause2 in &self.clauses {
                                if clause2.len() != 2 {
                                    continue;
                                }
                                let x2 = clause2[i2];
                                let y2 = -clause2[j2];
                                if y2 != y1 || x2 != x1 {
                                    continue;
                                }
                                for [i3, j3] in vec![[0, 1], [1, 0]] {
                                    for clause3 in &self.clauses {
                                        if clause3.len() != 2 {
                                            continue;
                                        }
                                        let x3 = clause3[i3];
                                        let z3 = -clause3[j3];
                                        if z3 != z1 || x3 != x1 {
                                            continue;
                                        }
                                        lits.push(x1);
                                    }
                                }
                            }
                        }
                    }
                }
                if !lits.is_empty() {
                    again = true;
                }
                for lit in lits {
                    self.assign_lit(lit);
                    result.assigned.push(lit);
                }
            }
            if !again {
                break;
            }
        }
        result
    }

    pub fn write_cnf<OUT: Write>(&self, out: &mut OUT) -> Result<(), std::io::Error> {
        let mut num_vars = 0;
        for clause in &self.clauses {
            for lit in clause {
                let var = lit.abs();
                if var > num_vars {
                    num_vars = var;
                }
            }
        }
        writeln!(out, "p cnf {} {}", num_vars, self.clauses.len())?;
        for clause in &self.clauses {
            for lit in clause {
                write!(out, "{} ", lit)?;
            }
            writeln!(out, "0")?;
        }
        Ok(())
    }
}

impl fmt::Display for Sat {
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

pub struct SatRules {
    rules: std::vec::Vec<(
        std::vec::Vec<std::vec::Vec<isize>>,
        isize,
        std::vec::Vec<std::vec::Vec<isize>>,
    )>,
}

impl SatRules {
    pub fn new() -> SatRules {
        SatRules {
            rules: vec![
                // a <-> b
                // (a -> b) and (b -> a)
                // (!a or b) and (!b or a)
                (vec![vec![-1, 2], vec![1, -2]], 1, vec![vec![2]]),
                // a <-> b or c
                // (a -> b or c) and (b or c -> a)
                // (!a or b or c) and ((!b and !c) or a)
                // (!a or b or c) and (!b or a) and (!c or a)
                (
                    vec![vec![-1, 2, 3], vec![-2, 1], vec![-3, 1]],
                    1,
                    vec![vec![2, 3]],
                ),
            ],
        }
    }
}
