use crate::_3Sat;
use std::collections::{HashMap, HashSet};
use std::fmt;

pub struct _2Sat {
    pub clauses: Vec<[isize; 2]>,
}

impl _2Sat {
    pub fn from_clauses(clauses: Vec<[isize; 2]>) -> Self {
        _2Sat { clauses }
    }

    pub fn from_3sat(sat: _3Sat) -> Self {
        let mut next_var = 1;
        for clause in &sat.clauses {
            for lit in clause {
                let lit2 = lit.abs();
                if lit2 >= next_var {
                    next_var = lit2 + 1;
                }
            }
        }
        let mut extra_map: HashMap<[isize; 2], isize> = HashMap::new();
        fn alloc_extra(
            extra_map: &mut HashMap<[isize; 2], isize>,
            next_var: &mut isize,
            mut x: isize,
            mut y: isize,
        ) -> isize {
            if x > y {
                std::mem::swap(&mut x, &mut y);
            }
            let key = [x, y];
            if let Some(r) = extra_map.get(&key) {
                return *r;
            }
            let r = *next_var;
            *next_var += 1;
            extra_map.insert(key, r);
            r
        }
        let mut result: Vec<[isize; 2]> = Vec::new();
        for [x, y, z] in sat.clauses {
            result.push([x, alloc_extra(&mut extra_map, &mut next_var, y, z)]);
            result.push([y, alloc_extra(&mut extra_map, &mut next_var, z, x)]);
            result.push([z, alloc_extra(&mut extra_map, &mut next_var, x, y)]);
        }
        _2Sat { clauses: result }
    }

    pub fn solve(&self) -> Option<HashSet<isize>> {
        Graph::from_2sat(self).solve()
    }
}

#[derive(Debug)]
struct Graph {
    node_map: HashMap<isize, Node>,
}

#[derive(Debug)]
struct Node {
    edges: Vec<isize>,
}

impl Graph {
    pub fn from_2sat(sat: &_2Sat) -> Graph {
        let mut node_map = HashMap::new();
        let insert_edge = |node_map: &mut HashMap<isize, Node>, node: isize, edge: isize| {
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
        for clause in &sat.clauses {
            insert_edge(&mut node_map, -clause[0], clause[1]);
            insert_edge(&mut node_map, -clause[1], clause[0]);
        }
        Graph { node_map }
    }

    pub fn solve(&self) -> Option<HashSet<isize>> {
        let mut vars = HashSet::new();
        for (ref var, _) in &self.node_map {
            vars.insert(var.abs());
        }
        let mut stack: Vec<isize> = vars.drain().collect();
        std::mem::drop(vars);
        let mut result = HashSet::new();
        loop {
            let var_op = stack.pop();
            if let Some(var) = var_op {
                if result.contains(&var) || result.contains(&-var) {
                    continue;
                }
                let mut visited = HashSet::new();
                let mut stack2 = vec![var];
                let mut failed = false;
                let mut first_pass = true;
                loop {
                    let at_op = stack2.pop();
                    if let Some(at) = at_op {
                        if visited.contains(&at) {
                            continue;
                        }
                        visited.insert(at);
                        if visited.contains(&-at) {
                            if first_pass {
                                stack2.clear();
                                visited.clear();
                                stack2.push(-var);
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

impl fmt::Display for _2Sat {
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
fn test_2sat() {
    let sat = _2Sat::from_clauses(vec![[1, 2], [2, 3], [3, 1], [-2, -2]]);
    if let Some(result) = sat.solve() {
        println!("{:?}", result);
    }
}
