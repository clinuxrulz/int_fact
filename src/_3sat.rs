use crate::_1InAllSat;
use crate::_2Sat;
use std::cmp::{max, min};
use std::collections::{HashMap, HashSet};
use std::fmt;

pub struct _3Sat {
    pub clauses: Vec<[isize; 3]>,
}

impl _3Sat {
    pub fn from_clauses(clauses: Vec<[isize; 3]>) -> Self {
        _3Sat { clauses }
    }

    pub fn from_sat_clauses(clauses: Vec<Vec<isize>>) -> Self {
        let mut result: Vec<[isize; 3]> = Vec::new();
        let mut next_var = 1;
        for clause in &clauses {
            for lit in clause {
                let lit2 = lit.abs();
                if lit2 >= next_var {
                    next_var = lit2 + 1;
                }
            }
        }
        for mut clause in clauses {
            if clause.is_empty() {
                result.push([0, 0, 0]);
            } else if clause.len() == 1 {
                result.push([clause[0]; 3]);
            } else if clause.len() == 2 {
                let x = clause[0];
                let y = clause[1];
                result.push([x, y, y]);
            } else if clause.len() == 3 {
                let x = clause[0];
                let y = clause[1];
                let z = clause[2];
                result.push([x, y, z]);
            } else {
                let mut link = next_var;
                next_var = next_var + 1;
                {
                    let x = clause.remove(0);
                    let y = clause.remove(0);
                    result.push([x, y, link]);
                }
                while !clause.is_empty() {
                    if clause.len() == 1 {
                        let x = clause.remove(0);
                        result.push([-link, x, x]);
                    } else if clause.len() == 2 {
                        let x = clause.remove(0);
                        let y = clause.remove(0);
                        result.push([-link, x, y]);
                    } else {
                        let x = clause.remove(0);
                        let y = -link;
                        let link = next_var;
                        next_var = next_var + 1;
                        result.push([x, y, link]);
                    }
                }
            }
        }
        _3Sat { clauses: result }
    }

    pub fn add_clause(&mut self, clause: [isize; 3]) {
        self.clauses.push(clause);
    }

    pub fn assign_lit(&mut self, lit: isize) {
        for i in (0..self.clauses.len()).rev() {
            let found = self.clauses[i].iter().any(|x| *x == lit);
            if found {
                self.clauses.remove(i);
            } else {
                let mut tmp: Vec<isize> = self.clauses[i]
                    .iter()
                    .filter(|x| **x != -lit)
                    .map(|x| *x)
                    .collect();
                if tmp.is_empty() {
                    continue;
                }
                while tmp.len() < 3 {
                    let tmp2 = tmp[0];
                    tmp.push(tmp2);
                }
                self.clauses[i][0] = tmp[0];
                self.clauses[i][1] = tmp[1];
                self.clauses[i][2] = tmp[2];
            }
        }
    }

    pub fn solve2(&self) -> Option<HashSet<isize>> {
        let graph = Graph::from_3sat(self);
        let result_op = graph.solve();
        result_op.map(|result| {
            let tmp: HashSet<isize> = result
                .iter()
                .filter_map(|&(ref not, ref x, ref y)| {
                    if *x == *y {
                        if *not {
                            Some(-*x)
                        } else {
                            Some(*x)
                        }
                    } else {
                        None
                    }
                })
                .collect();
            tmp
        })
    }

    pub fn is_sat(&self) -> bool {
        let mut sat = _1InAllSat::from_3sat(self);
        sat.solve().is_some()
    }

    pub fn solve(&self) -> Option<HashSet<isize>> {
        let mut result: HashSet<isize> = HashSet::new();
        let mut vars: HashSet<isize> = HashSet::new();
        let mut next_var = 1;
        for clause in &self.clauses {
            for lit in clause {
                let lit2 = lit.abs();
                vars.insert(lit2);
                if lit2 >= next_var {
                    next_var = lit2 + 1;
                }
            }
        }
        for var in vars {
            let sat1 = _2Sat::from_clauses(
                self.clauses
                    .iter()
                    .filter_map(|&[ref x, ref y, ref z]| {
                        if *x == -var {
                            Some([*y, *z])
                        } else if *y == -var {
                            Some([*z, *x])
                        } else if *z == -var {
                            Some([*x, *y])
                        } else {
                            None
                        }
                    })
                    .chain(result.iter().map(|x| [*x, *x]))
                    .collect(),
            );
            let sat2 = _2Sat::from_clauses(
                self.clauses
                    .iter()
                    .filter_map(|&[ref x, ref y, ref z]| {
                        if *x == var {
                            Some([*y, *z])
                        } else if *y == var {
                            Some([*z, *x])
                        } else if *z == var {
                            Some([*x, *y])
                        } else {
                            None
                        }
                    })
                    .chain(result.iter().map(|x| [*x, *x]))
                    .collect(),
            );
            let sat1_unsat = sat1.solve().is_none();
            let sat2_unsat = sat2.solve().is_none();
            std::mem::drop(sat1);
            std::mem::drop(sat2);
            if sat1_unsat {
                if sat2_unsat {
                    return None;
                } else {
                    result.insert(-var);
                }
            } else {
                if sat2_unsat {
                    result.insert(var);
                } else {
                    // do nothing.
                }
            }
        }
        Some(result)
    }
}

#[derive(Debug)]
struct Graph {
    node_map: HashMap<(bool, isize, isize), Node>,
}

#[derive(Debug)]
struct Node {
    edges: Vec<(bool, isize, isize)>,
}

impl Graph {
    pub fn implies(lhs: &(bool, isize, isize), rhs: &(bool, isize, isize)) -> bool {
        let mut state: Vec<(isize, bool)> = Vec::new();
        for lit in [lhs.1, lhs.2, rhs.1, rhs.2].iter() {
            let var = lit.abs();
            let found = state.iter().any(|&(ref var2, _)| var.eq(var2));
            if !found {
                state.push((var, false));
            }
        }
        fn inc_state(state: &mut Vec<(isize, bool)>) -> bool {
            let mut i = 0;
            let mut overflow = true;
            while i < state.len() {
                state[i].1 = !state[i].1;
                if state[i].1 {
                    overflow = false;
                    break;
                }
                i += 1;
            }
            overflow
        }
        fn eval_lit(state: &Vec<(isize, bool)>, lit: isize) -> bool {
            let var = lit.abs();
            let val = state
                .iter()
                .find_map(|&(ref var2, ref val)| if var2.eq(&var) { Some(*val) } else { None })
                .unwrap();
            if lit < 0 {
                !val
            } else {
                val
            }
        }
        fn eval(state: &Vec<(isize, bool)>, expr: &(bool, isize, isize)) -> bool {
            let a = eval_lit(state, expr.1);
            let b = eval_lit(state, expr.2);
            let c;
            if expr.1 < expr.2 {
                c = a || b;
            } else if expr.1 > expr.2 {
                c = a && b;
            } else {
                c = a;
            }
            if expr.0 {
                !c
            } else {
                c
            }
        }
        loop {
            let a = eval(&state, lhs);
            let b = eval(&state, rhs);
            if a && !b {
                return false;
            }
            if inc_state(&mut state) {
                break;
            }
        }
        true
    }

    pub fn from_3sat(sat: &_3Sat) -> Graph {
        let mut node_map = HashMap::new();
        let insert_edge = |node_map: &mut HashMap<(bool, isize, isize), Node>,
                           node: (bool, isize, isize),
                           edge: (bool, isize, isize)| {
            let found;
            if let Some(node2) = node_map.get_mut(&node) {
                found = true;
                node2.edges.push(edge);
            } else {
                found = false;
            }
            if !found {
                let node2 = Node { edges: vec![edge] };
                node_map.insert(node, node2);
            }
        };
        let mut max_var = 1;
        for clause in &sat.clauses {
            for lit in clause {
                let var = lit.abs();
                if var > max_var {
                    max_var = var;
                }
            }
        }
        for lhs_bool in [false, true].iter() {
            let lhs_bool = *lhs_bool;
            for lhs_a in -max_var..(max_var + 1) {
                if lhs_a == 0 {
                    continue;
                }
                for lhs_b in -max_var..(max_var + 1) {
                    if lhs_b == 0 || lhs_b == -lhs_a {
                        continue;
                    }
                    let lhs = (lhs_bool, lhs_a, lhs_b);
                    for rhs_bool in [false, true].iter() {
                        let rhs_bool = *rhs_bool;
                        for rhs_a in -max_var..(max_var + 1) {
                            if rhs_a == 0 {
                                continue;
                            }
                            for rhs_b in -max_var..(max_var + 1) {
                                if rhs_b == 0 || rhs_b == -rhs_a {
                                    continue;
                                }
                                let rhs = (rhs_bool, rhs_a, rhs_b);
                                let tmp = Self::implies(&lhs, &rhs);
                                if tmp {
                                    insert_edge(&mut node_map, lhs, rhs);
                                }
                            }
                        }
                    }
                }
            }
        }
        for clause in &sat.clauses {
            let [x, y, z] = *clause;
            let a = min(x, y);
            let b = max(x, y);
            let c = min(y, z);
            let d = max(y, z);
            let e = min(z, x);
            let f = max(z, x);
            // not (x or y) -> z
            // not x and not y -> z
            for not1 in [false, true].iter() {
                let not1 = *not1;
                let s1 = if not1 { -1 } else { 1 };
                for not2 in [false, true].iter() {
                    let not2 = *not2;
                    let s2 = if not2 { -1 } else { 1 };
                    insert_edge(
                        &mut node_map,
                        (not1, -s1 * a, -s1 * b),
                        (not2, s2 * z, s2 * z),
                    );
                    insert_edge(
                        &mut node_map,
                        (not1, -s1 * z, -s1 * z),
                        (not2, s2 * a, s2 * b),
                    );
                    insert_edge(
                        &mut node_map,
                        (not1, -s1 * c, -s1 * d),
                        (not2, s2 * x, s2 * x),
                    );
                    insert_edge(
                        &mut node_map,
                        (not1, -s1 * x, -s1 * x),
                        (not2, s2 * c, s2 * d),
                    );
                    insert_edge(
                        &mut node_map,
                        (not1, -s1 * e, -s1 * f),
                        (not2, s2 * y, s2 * y),
                    );
                    insert_edge(
                        &mut node_map,
                        (not1, -s1 * y, -s1 * y),
                        (not2, s2 * e, s2 * f),
                    );
                }
            }
        }
        Graph { node_map }
    }

    pub fn solve(&self) -> Option<HashSet<(bool, isize, isize)>> {
        let mut max_var = 1;
        for (ref lit, _) in &self.node_map {
            let var1 = lit.1.abs();
            let var2 = lit.2.abs();
            if var1 > max_var {
                max_var = var1;
            }
            if var2 > max_var {
                max_var = var2;
            }
        }
        let mut stack: Vec<(isize, isize)> = Vec::new();
        for i in 1..(max_var + 1) {
            let mut a = i + 1;
            let mut b = i;
            if a > max_var {
                a = b;
                b = 1;
            }
            stack.push((a, b));
        }
        let mut result: HashSet<(bool, isize, isize)> = HashSet::new();
        loop {
            let var_op = stack.pop();
            if let Some(var) = var_op {
                if result.contains(&(false, var.0, var.1))
                    || result.contains(&(true, -var.0, -var.1))
                {
                    continue;
                }
                let mut visited: HashSet<(bool, isize, isize)> = HashSet::new();
                let mut stack2 = vec![(false, var.0, var.1)];
                let mut failed = false;
                let mut first_pass = true;
                loop {
                    let at_op = stack2.pop();
                    if let Some(at) = at_op {
                        if visited.contains(&at) {
                            continue;
                        }
                        visited.insert(at);
                        visited.insert((!at.0, -at.1, -at.2));
                        if visited.contains(&(!at.0, at.1, at.2))
                            || visited.contains(&(at.0, -at.1, -at.2))
                        {
                            if first_pass {
                                stack2.clear();
                                visited.clear();
                                stack2.push((true, var.0, var.1));
                                first_pass = false;
                            } else {
                                failed = true;
                                break;
                            }
                        }
                        if let Some(&Node { ref edges }) = self.node_map.get(&at) {
                            for edge in edges {
                                stack2.push(*edge);
                            }
                        }
                    } else {
                        break;
                    }
                }
                if failed {
                    return None;
                }
                for at in visited {
                    result.insert(at);
                }
            } else {
                break;
            }
        }
        Some(result)
    }
}

impl fmt::Display for _3Sat {
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
fn test_3sat() {
    let sat = _3Sat::from_clauses(vec![
        [1, 2, 3],
        [1, 2, -3],
        [1, -2, 3],
        [1, -2, -3],
        [-1, 2, 3],
        [-1, -2, 3],
        [-1, -2, -3],
    ]);
    println!("{}", sat);
    println!();
    println!("{:?}", sat.solve());
}

#[test]
fn test_3graph() {
    let sat = _3Sat::from_clauses(vec![
        [1, 2, 3],
        [1, 2, -3],
        [1, -2, 3],
        [1, -2, -3],
        [-1, 2, 3],
        [-1, -2, 3],
        [-1, -2, -3],
    ]);
    println!("{}", sat);
    println!();
    let graph = Graph::from_3sat(&sat);
    println!("{:?}", graph);
    println!();
    println!("{:?}", graph.solve());
    println!();
    println!("{:?}", sat.solve2());
}
