use std::collections::{HashMap, HashSet};
use crate::{CnfFormula, Lit, Var};
use crate::{Rng};

pub struct SolverCtx<'a> {
    cnf: &'a CnfFormula,
    variables: Vec<Var>,
    units: HashSet<Lit>,
    assignments: HashSet<Lit>,
    watches: HashMap<Lit,Vec<usize>>,
    conflicts: HashSet<usize>,
    forced_assignments: HashSet<Lit>,
    rng: Rng,
}

impl<'a> SolverCtx<'a> {
    pub fn new(cnf: &'a CnfFormula) -> SolverCtx<'a> {
        let mut variable_set: HashSet<Var> = HashSet::new();
        let mut units: HashSet<Lit> = HashSet::new();
        for clause in cnf {
            for lit in clause {
                variable_set.insert(lit.var());
            }
            if clause.len() == 1 {
                units.insert(clause[0]);
            }
        }
        let mut variables: Vec<Var> = Vec::new();
        for var in variable_set {
            variables.push(var);
        }
        variables.sort();
        SolverCtx {
            cnf,
            variables,
            units,
            assignments: HashSet::new(),
            watches: HashMap::new(),
            conflicts: HashSet::new(),
            forced_assignments: HashSet::new(),
            rng: Rng::new(),
        }
    }

    pub fn solve(&mut self) -> Option<Vec<Lit>> {
        self.init_watches();
        self.assignments.clear();
        let variables = self.variables.clone();
        const MAX_ITERATIONS: usize = 100000;
        let units = self.units.clone();
        for unit in &units {
            self.assign_lit(*unit);
        }
        for lit in &self.assignments {
            self.units.insert(*lit);
        }
        println!("{:?}", self.assignments);
        for _it in 1..(MAX_ITERATIONS+1) {
            for var in &variables {
                let mut lit: isize = (*var).into();
                if (self.rng.gen() & 1) == 0 {
                    lit = -lit;
                }
                let lit = Lit::from(lit);
                if self.assignments.contains(&lit) || self.assignments.contains(&lit.negated()) {
                    continue;
                }
                self.assign_lit(lit);
                if !self.conflicts.is_empty() {
                    break;
                }
            }
            let mut delayed_assignments: Vec<Lit> = Vec::new();
            let mut conflicts: Vec<usize> = Vec::new();
            println!("{} conflicts", self.conflicts.len());
            for clause_id in &self.conflicts {
                conflicts.push(*clause_id);
                println!("conflict {}: {:?}", clause_id, self.cnf[*clause_id]);
            }
            if !conflicts.is_empty() {
                let idx = (self.rng.gen() as usize) % conflicts.len();
                let x = conflicts[idx];
                conflicts.clear();
                conflicts.push(x);
            }
            for clause_idx in &conflicts {
                let clause = &self.cnf[*clause_idx];
                if clause.into_iter().any(|lit| !self.assignments.contains(lit)) {
                    let flip_idx = (self.rng.gen() as usize) % clause.len();
                    let lit = clause[flip_idx];
                    if !self.units.contains(&lit.negated()) {
                        println!("try flip {:?}", lit);
                        //crate::solver1::pause();
                        self.unassign_lit(lit.negated());
                        self.assign_lit(lit);
                        break;
                    }
                }
            }
            if self.conflicts.is_empty() && self.assignments.len() == self.variables.len() {
                let mut result: Vec<Lit> = Vec::with_capacity(self.assignments.len());
                for lit in &self.assignments {
                    result.push(*lit);
                }
                result.sort_by(|a,b| a.var().cmp(&b.var()));
                let tmp: Vec<isize> =
                    result.iter().map(|x| { let y: isize = (*x).into(); y}).collect();
                println!("solved {:?}", tmp);
                return Some(result);
            }
        }
        println!("max iterations exceeded");
        None
    }

    fn verify_conflicts(&self) {
        let mut clause_id: usize = 0;
        for clause in self.cnf {
            let conflict = clause.into_iter().all(|lit| self.assignments.contains(&lit.negated()));
            if conflict {
                if !self.conflicts.contains(&clause_id) {
                    let mut tmp: Vec<isize> =
                        self.assignments.iter().map(|x| { let y: isize = (*x).into(); y}).collect();
                    tmp.sort_by(|a,b| a.abs().cmp(&b.abs()));
                    println!("assignments: {:?}", tmp);
                    panic!("missing conflict {}: {:?}", clause_id, self.cnf[clause_id]);
                }
            } else {
                if self.conflicts.contains(&clause_id) {
                    let mut tmp: Vec<isize> =
                        self.assignments.iter().map(|x| { let y: isize = (*x).into(); y}).collect();
                    tmp.sort_by(|a,b| a.abs().cmp(&b.abs()));
                    println!("assignments: {:?}", tmp);
                    panic!("false conflict {}: {:?}", clause_id, self.cnf[clause_id]);
                }
            }
            clause_id += 1;
        }
    }

    pub fn assign_lit(&mut self, lit: Lit) {
        let mut assign_queue = vec![lit];
        while !assign_queue.is_empty() {
            let lit = assign_queue.remove(0);
            if self.assignments.contains(&lit) || self.assignments.contains(&lit.negated()) {
                continue;
            }
            self.assignments.insert(lit);
            Self::shift_watches(
                &self.cnf,
                &mut self.watches,
                lit.negated(),
                &mut self.conflicts,
                &self.assignments,
                &mut self.forced_assignments
            );
            for lit2 in &self.forced_assignments {
                assign_queue.push(*lit2);
            }
            self.forced_assignments.clear();
        }
        self.verify_conflicts();
    }

    pub fn unassign_lit(&mut self, lit: Lit) {
        println!("in unassign_lit");
        self.assignments.remove(&lit);
        let conflicts = self.conflicts.clone();
        let lit_negated = lit.negated();
        for clause_id in conflicts {
            let clause = &self.cnf[clause_id];
            if clause.into_iter().any(|lit2| *lit2 == lit_negated) {
                self.conflicts.remove(&clause_id);
                for lit2 in clause {
                    if *lit2 == lit_negated {
                        continue;
                    }
                    let mut found = false;
                    if let Some(x) = self.watches.get_mut(&lit2) {
                        if let Some(i) = x.iter().position(|clause2_id| *clause2_id == clause_id) {
                            x.remove(i);
                            found = true;
                        }
                    }
                    if found {
                        let found2;
                        if let Some(x) = self.watches.get_mut(&lit_negated) {
                            x.push(clause_id);
                            found2 = true;
                        } else {
                            found2 = false;
                        }
                        if !found2 {
                            self.watches.insert(lit_negated, vec![clause_id]);
                        }
                        break;
                    }
                }
            }
        }
        self.verify_conflicts();
        println!("out unassign_lit");
    }

    pub fn init_watches(&mut self) {
        self.watches.clear();
        for clause_idx in 0..self.cnf.len() {
            let clause = &self.cnf[clause_idx];
            if clause.len() >= 2 {
                Self::add_watch(&mut self.watches, clause_idx, clause[0]);
                Self::add_watch(&mut self.watches, clause_idx, clause[1]);
            }
        }
    }

    fn add_watch(watches: &mut HashMap<Lit,Vec<usize>>, clause_idx: usize, lit: Lit) {
        let found;
        if let Some(x) = watches.get_mut(&lit) {
            x.push(clause_idx);
            found = true;
        } else {
            found = false;
        }
        if !found {
            watches.insert(lit, vec![clause_idx]);
        }
    }

    fn shift_watches(cnf: &CnfFormula, watches: &mut HashMap<Lit,Vec<usize>>, lit: Lit, conflicts: &mut HashSet<usize>, assignments: &HashSet<Lit>, forced_assignments: &mut HashSet<Lit>) {
        let clause_ids: Vec<usize>;
        if let Some(clause_ids2) = watches.get(&lit) {
            clause_ids = clause_ids2.clone();
        } else {
            return;
        }
        println!("assignments: {:?}", assignments);
        for clause_id in clause_ids {
            let mut shift_to_lit_op: Option<Lit> = None;
            let clause = &cnf[clause_id];
            let mut other_watch_op: Option<Lit> = None;
            for lit2 in clause {
                if *lit2 == lit || assignments.contains(&lit2.negated()) {
                    continue;
                }
                let found;
                if let Some(x) = watches.get(lit2) {
                    found = x.iter().all(|clause_id2| *clause_id2 != clause_id);
                    if !found {
                        println!("watches: {:?} {:?} {:?}", lit, lit2, cnf[clause_id]);
                        other_watch_op = Some(*lit2);
                    }
                } else {
                    found = true;
                }
                if found {
                    if shift_to_lit_op.is_none() {
                        shift_to_lit_op = Some(*lit2);
                    }
                }
            }
            if let Some(shift_to_lit) = shift_to_lit_op {
                println!("shift to {:?}", shift_to_lit);
                if let Some(x) = watches.get_mut(&lit) {
                    x.retain(|clause_id2| *clause_id2 != clause_id);
                }
                let found;
                if let Some(x) = watches.get_mut(&shift_to_lit) {
                    x.push(clause_id);
                    found = true;
                } else {
                    found = false;
                }
                if !found {
                    watches.insert(shift_to_lit, vec![clause_id]);
                }
            } else {
                if let Some(other_watch) = other_watch_op {
                    println!("forced id {}, lit {:?}", clause_id, other_watch);
                    forced_assignments.insert(other_watch);
                } else {
                    //println!("conflict id {}", clause_id);
                    conflicts.insert(clause_id);
                }
            }
        }
        //crate::solver1::pause();
    }
}

#[test]
fn test_solver2() {
    let cnf = CnfFormula::from(vec![
        vec![1, 4],
        vec![1, -3, -8],
        vec![1, 8, 12],
        vec![2, 11],
        vec![-7, -3, 9],
        vec![-7, 8, -9],
        vec![7, 8, -10],
        vec![7, 10, -12],
    ]);
    println!("{}", cnf);
    println!();
    let mut solver_ctx = SolverCtx::new(&cnf);
    println!("result: {:?}", solver_ctx.solve());
}
