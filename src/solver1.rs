use crate::Rng;
use crate::Sat;
use std::collections::{HashMap, HashSet};

pub struct SolverCtx {
    clauses: Vec<Vec<isize>>,
    learnt_clauses: Vec<Vec<isize>>,
    removed_clauses: HashSet<usize>,
    vars: Vec<isize>,
    assignments: HashSet<isize>,
    decisions: Vec<isize>,
    confirmed_units: Vec<isize>,
    conflicting_clauses: Vec<usize>,
    // map from literial to clause indices containing them
    watches: HashMap<isize, Vec<usize>>,
    units: Vec<(usize, isize)>,
    impl_graph: ImplGraph,
    rng: Rng,
}

#[derive(Debug)]
enum Op {
    AssignLit(isize),
    RemoveClause(usize),
    EmptyClause,
}

impl SolverCtx {
    pub fn new() -> SolverCtx {
        SolverCtx {
            clauses: Vec::new(),
            learnt_clauses: Vec::new(),
            removed_clauses: HashSet::new(),
            vars: Vec::new(),
            assignments: HashSet::new(),
            decisions: Vec::new(),
            confirmed_units: Vec::new(),
            conflicting_clauses: Vec::new(),
            watches: HashMap::new(),
            units: Vec::new(),
            impl_graph: ImplGraph::new(),
            rng: Rng::new(),
        }
    }

    pub fn add_clauses(&mut self, mut sat: Sat) {
        self.clauses.append(&mut sat.clauses);
    }

    pub fn solve(&mut self) -> Option<Vec<isize>> {
        self.init_watches();
        let mut num_vars: usize = 0;
        let mut vars: HashSet<isize> = HashSet::new();
        for clause in &self.clauses {
            for lit in clause {
                let var = lit.abs() as usize;
                vars.insert(var as isize);
                if var > num_vars {
                    num_vars = var;
                }
            }
        }
        self.vars.clear();
        for var in vars {
            self.vars.push(var);
        }
        self.vars.sort();
        while let Some(lit) = self.pick_lit() {
            self.assign_lit(lit);
            self.bcp();
            if !self.conflicting_clauses.is_empty() {
                //println!("{:?}", self.impl_graph);
                //println!("bcp {:?}", self.bcp_decisions);
                //println!("conflicting clauses {:?}", self.conflicting_clauses);
                self.learn_and_backtrack();
            }
            if self.pick_lit().is_none() && !self.confirm_result() {
                self.assignments.clear();
                self.decisions.clear();
                self.impl_graph.clear();
                for unit in self.confirmed_units.clone() {
                    if !self.assignments.contains(&unit) {
                        self.assign_lit(unit);
                    }
                }
            }
        }
        if self.confirm_result() {
            println!("SAT");
        } else {
            println!("UNSAT");
        }
        let mut result: Vec<isize> = self.assignments.iter().map(|x| *x).collect();
        result.sort_by(|a, b| a.abs().cmp(&b.abs()));
        Some(result)
    }

    fn confirm_result(&self) -> bool {
        for clause in &self.clauses {
            let match_ = clause.iter().any(|lit| self.assignments.contains(lit));
            if !match_ {
                return false;
            }
        }
        true
    }

    fn init_watches(&mut self) {
        for i in 0..self.clauses.len() {
            let clause = &self.clauses[i];
            if clause.len() >= 1 {
                Self::add_watch(&mut self.watches, clause[0], i);
            }
            if clause.len() >= 2 {
                Self::add_watch(&mut self.watches, clause[1], i);
            }
        }
    }

    fn add_watch(watches: &mut HashMap<isize, Vec<usize>>, lit: isize, clause_id: usize) {
        let mut found = false;
        if let Some(x) = watches.get_mut(&lit) {
            x.push(clause_id);
            found = true;
        }
        if !found {
            watches.insert(lit, vec![clause_id]);
        }
    }

    fn pick_lit(&mut self) -> Option<isize> {
        let mut pick: Vec<isize> = Vec::new();
        for i in &self.vars {
            let i = *i;
            if !(self.assignments.contains(&i) || self.assignments.contains(&-i)) {
                pick.push(i);
            }
        }
        if pick.is_empty() {
            return None;
        }
        let i = (self.rng.gen() % (pick.len() as u32)) as usize;
        let sign = self.rng.gen() & 1;
        let var = pick[i];
        let lit = if sign == 0 { -var } else { var };
        Some(lit)
        /*
        for i in 0..self.clauses.len() {
            if self.removed_clauses.contains(&i) {
                continue;
            }
            let clause = &self.clauses[i];
            for lit in clause {
                if !(self.assignments.contains(lit) || self.assignments.contains(&-*lit)) {
                    return Some(*lit);
                }
            }
        }
        None*/
    }

    fn assign_lit(&mut self, lit: isize) {
        //println!("assign_lit({});", lit);
        self.assignments.insert(lit);
        self.decisions.push(lit);
        self.shift_watches(-lit);
    }

    fn shift_watches(&mut self, lit: isize) {
        let clause_ids_op = self.watches.get(&lit).map(|x| x.clone());
        if let Some(clause_ids) = clause_ids_op {
            for clause_id in clause_ids {
                self.shift_watch(lit, clause_id);
            }
        }
    }

    fn shift_watch(&mut self, lit: isize, clause_id: usize) {
        if !self.is_watched(lit, clause_id) {
            return;
        }
        enum WatchStatus {
            NoWatch,
            SingleWatch(isize),
            ManyWatches,
        }
        let mut watch_status = WatchStatus::NoWatch;
        let mut can_watch_op: Option<isize> = None;
        let mut others_for_impl: Vec<isize> = Vec::new();
        for lit2 in self.get_clause(clause_id) {
            if *lit2 == lit {
                continue;
            }
            if self.is_watched(*lit2, clause_id) && !self.assignments.contains(&-*lit2) {
                match watch_status {
                    WatchStatus::NoWatch => {
                        watch_status = WatchStatus::SingleWatch(*lit2);
                    }
                    WatchStatus::SingleWatch(_) => {
                        watch_status = WatchStatus::ManyWatches;
                    }
                    _ => {}
                }
            } else if !self.is_watched(*lit2, clause_id)
                && !self.assignments.contains(&-lit2)
                && can_watch_op.is_none()
            {
                can_watch_op = Some(*lit2);
            } else if self.assignments.contains(&-lit2) {
                others_for_impl.push(*lit2);
            }
        }
        if let Some(can_watch) = can_watch_op {
            if let Some(x) = self.watches.get_mut(&lit) {
                x.retain(|clause_id2| *clause_id2 != clause_id);
            }
            Self::add_watch(&mut self.watches, can_watch, clause_id);
        } else {
            match watch_status {
                WatchStatus::NoWatch => {
                    self.conflicting_clauses.push(clause_id);
                    self.impl_graph.remove_clause(clause_id);
                    self.units
                        .retain(|&(ref clause2_id, _)| *clause2_id != clause_id);
                }
                WatchStatus::SingleWatch(lit2) => {
                    self.impl_graph.add_impl(clause_id, lit2);
                    self.units.push((clause_id, lit2));
                }
                _ => {}
            }
        }
    }

    fn is_watched(&self, lit: isize, clause_id: usize) -> bool {
        self.watches
            .get(&lit)
            .map(|clause_ids| clause_ids.iter().any(|clause_id2| *clause_id2 == clause_id))
            .unwrap_or(false)
    }

    fn get_clause(&self, clause_id: usize) -> &Vec<isize> {
        &self.clauses[clause_id]
    }

    fn bcp(&mut self) {
        let mut units = Vec::new();
        while !self.units.is_empty() {
            units.clear();
            std::mem::swap(&mut units, &mut self.units);
            for unit in &units {
                if self.assignments.contains(&-unit.1) || self.assignments.contains(&unit.1) {
                    continue;
                }
                self.assign_lit(unit.1);
            }
        }
    }

    fn learn_and_backtrack(&mut self) {
        let mut learnt_clause_op: Option<Vec<isize>> = None;
        'loop1: for clause_id in &self.conflicting_clauses {
            let clause = self.get_clause(*clause_id);
            /*
            let lit_op = self.impl_graph.clause_implies_lit_map.get(&clause_id);
            if lit_op.is_none() {
                println!("manual conflict");
                continue;
            }
            let lit = *lit_op.unwrap();*/
            let mut clause_was_learnt = false;
            let mut learnt_clause = clause.clone();
            let mut other_lits: Vec<isize> = clause
                .iter() /*.filter(|lit2| **lit2 != lit)*/
                .map(|x| *x)
                .collect();
            println!("other_lits {:?}", other_lits);
            loop {
                let mut again = false;
                for lit2 in &other_lits {
                    let next_clauses_op = self.impl_graph.lit_implied_by_clauses_map.get(&-*lit2);
                    if let Some(next_clauses) = next_clauses_op {
                        println!("{} implied by clause {}", -*lit2, next_clauses[0]);
                        let next_clause = self.get_clause(next_clauses[0]);
                        println!(
                            "resolve {:?} and {:?} via {}",
                            learnt_clause, next_clause, lit2
                        );
                        learnt_clause.retain(|lit3| *lit3 != *lit2);
                        for lit3 in next_clause {
                            if *lit3 == -*lit2 {
                                continue;
                            }
                            learnt_clause.push(*lit3);
                        }
                        learnt_clause.sort();
                        learnt_clause.dedup();
                        learnt_clause.sort_by(|a, b| a.abs().cmp(&b.abs()));
                        if !learnt_clause.is_empty() {
                            for i in 0..learnt_clause.len() - 1 {
                                if learnt_clause[i] == -learnt_clause[i + 1] {
                                    continue 'loop1;
                                }
                            }
                        }
                        clause_was_learnt = true;
                        //println!("partial learnt_clause {:?}", learnt_clause);
                        //pause();
                        //again = true;
                    }
                }
                if !again {
                    break;
                }
                other_lits.clear();
                for lit2 in &learnt_clause {
                    other_lits.push(*lit2);
                }
            }
            if clause_was_learnt {
                println!("learnt_clause {:?}", learnt_clause);
                learnt_clause_op = Some(learnt_clause);
                //pause();
            }
            break;
        }
        if let Some(learnt_clause) = learnt_clause_op {
            self.clauses.push(learnt_clause.clone());
            let learnt_id = self.clauses.len() - 1;
            if self.clauses[learnt_id].len() >= 2 {
                Self::add_watch(&mut self.watches, self.clauses[learnt_id][0], learnt_id);
                Self::add_watch(&mut self.watches, self.clauses[learnt_id][1], learnt_id);
            }
            if learnt_clause.len() == 1 {
                self.confirmed_units.push(learnt_clause[0]);
            }
            let mut rewind_to_op: Option<usize> = None;
            for i in 0..self.decisions.len() {
                let lit = self.decisions[i];
                if learnt_clause.iter().any(|lit2| *lit2 == -lit) {
                    rewind_to_op = Some(i);
                    break;
                }
            }
            if let Some(rewind_to) = rewind_to_op {
                //let rewind_to = 0;
                let mut last_lit_op = None;
                while self.decisions.len() > rewind_to {
                    let lit = self.decisions.pop().unwrap();
                    self.assignments.remove(&lit);
                    self.impl_graph.remove_lit(lit);
                    last_lit_op = Some(lit);
                }
                if let Some(lit) = last_lit_op {
                    self.conflicting_clauses.clear();
                    self.assign_lit(-lit);
                }
            }
            for unit in self.confirmed_units.clone() {
                if !self.assignments.contains(&unit) {
                    self.assign_lit(unit);
                }
            }
        }
    }
}

struct SearchSpace {
    at: usize,
    min: Vec<bool>,
    max: usize,
    done: bool,
}

impl SearchSpace {
    fn new(max: usize) -> SearchSpace {
        SearchSpace {
            at: 0,
            min: Vec::new(),
            max: max - 1,
            done: false,
        }
    }

    fn pick(&mut self) -> Option<isize> {
        if self.done {
            return None;
        }
        while self.min.len() <= self.at {
            self.min.push(false);
        }
        let r = if self.min[self.at] {
            (self.at + 1) as isize
        } else {
            -((self.at + 1) as isize)
        };
        self.at += 1;
        if self.at > self.max {
            loop {
                self.at -= 1;
                let again = self.min[self.at] && self.at > 0;
                if self.min[self.at] && self.at == 0 {
                    self.done = true;
                }
                self.min[self.at] = !self.min[self.at];
                if !again {
                    break;
                }
            }
        }
        Some(r)
    }

    fn conflict(&mut self) {
        while self.min.len() <= self.at {
            self.min.push(false);
        }
        for i in (self.at + 1)..self.min.len() {
            self.min[i] = true;
        }
        /*
        loop {
            let again = self.min[self.at] && self.at > 0;
            self.min[self.at] = !self.min[self.at];
            if !again {
                self.at -= 1;
                break;
            }
        }*/
    }
}

#[derive(Debug)]
struct ImplGraph {
    clause_implies_lit_map: HashMap<usize, isize>,
    lit_implied_by_clauses_map: HashMap<isize, Vec<usize>>,
}

impl ImplGraph {
    fn new() -> ImplGraph {
        ImplGraph {
            clause_implies_lit_map: HashMap::new(),
            lit_implied_by_clauses_map: HashMap::new(),
        }
    }

    fn clear(&mut self) {
        self.clause_implies_lit_map.clear();
        self.lit_implied_by_clauses_map.clear();
    }

    fn add_impl(&mut self, clause_id: usize, lit: isize) {
        {
            let found;
            if let Some(x) = self.clause_implies_lit_map.get_mut(&clause_id) {
                *x = lit;
                found = true;
            } else {
                found = false;
            }
            if !found {
                self.clause_implies_lit_map.insert(clause_id, lit);
            }
        }
        {
            let found;
            if let Some(x) = self.lit_implied_by_clauses_map.get_mut(&lit) {
                if x.iter().all(|clause_id2| *clause_id2 != clause_id) {
                    x.push(clause_id);
                }
                found = true;
            } else {
                found = false;
            }
            if !found {
                self.lit_implied_by_clauses_map.insert(lit, vec![clause_id]);
            }
        }
    }

    fn remove_clause(&mut self, clause_id: usize) {
        if let Some(lit) = self.clause_implies_lit_map.get(&clause_id) {
            let mut is_empty = false;
            if let Some(x) = self.lit_implied_by_clauses_map.get_mut(lit) {
                x.retain(|clause2_id| *clause2_id != clause_id);
                is_empty = x.is_empty();
            }
            if is_empty {
                self.lit_implied_by_clauses_map.remove(lit);
            }
        }
        self.clause_implies_lit_map.remove(&clause_id);
    }

    fn remove_lit(&mut self, lit: isize) {
        if let Some(x1) = self.lit_implied_by_clauses_map.get(&lit) {
            for clause_id in x1 {
                self.clause_implies_lit_map.remove(clause_id);
            }
        }
        self.lit_implied_by_clauses_map.remove(&lit);
    }
}

use std::io::{stdin, stdout, Read, Write};

pub fn pause() {
    let mut stdout = stdout();
    stdout.write(b"Press Enter to continue...").unwrap();
    stdout.flush().unwrap();
    stdin().read(&mut [0]).unwrap();
}

#[test]
fn test_solver1() {
    let sat = Sat::from_clauses(vec![
        vec![1, 4],
        vec![1, -3, -8],
        vec![1, 8, 12],
        vec![2, 11],
        vec![-7, -3, 9],
        vec![-7, 8, -9],
        vec![7, 8, -10],
        vec![7, 10, -12],
    ]);
    println!("{}", sat);
    println!();

    use crate::{CnfFormula, Lit};
    fn erase_var(cnf: &mut CnfFormula, var: isize) {
        let mut dnf1 = cnf.duel();
        let mut dnf2 = dnf1.clone();
        dnf1.assign_lit(Lit::from(var));
        dnf2.assign_lit(Lit::from(-var));
        dnf1.append(&mut dnf2);
        dnf1.sort();
        dnf1.dedup();
        *cnf = dnf1.duel();
    }
    let mut cnf2 = CnfFormula::from(sat.clauses.clone());
    erase_var(&mut cnf2, 7);
    erase_var(&mut cnf2, 1);
    
    println!("test {}", cnf2);

    let mut solver_ctx = SolverCtx::new();
    solver_ctx.add_clauses(sat);
    println!("result: {:?}", solver_ctx.solve());
}

#[test]
fn test_search_space() {
    let mut ss = SearchSpace::new(3);
    while let Some(x) = ss.pick() {
        println!("{}", x);
    }
}
