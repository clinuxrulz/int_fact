use std::collections::HashMap;

#[derive(Debug)]
pub struct SatTree {
    next_id: usize,
    tree_map: HashMap<usize, Tree>,
    branch_map: HashMap<usize, Branch>,
    root_op: Option<usize>,
}

#[derive(Clone, Copy, Debug)]
struct Tree {
    id: usize,
    root: Node,
}

#[derive(Clone, Copy, Debug)]
enum Node {
    Tree(usize),
    Branch(usize),
    Leaf(bool),
}

#[derive(Clone, Copy, Debug)]
struct Branch {
    id: usize,
    if_lit: isize,
    then: Node,
    else_: Node,
}

impl SatTree {
    pub fn new() -> SatTree {
        SatTree {
            next_id: 0,
            tree_map: HashMap::new(),
            branch_map: HashMap::new(),
            root_op: None,
        }
    }

    pub fn from_clauses(clauses: &Vec<Vec<isize>>) -> SatTree {
        let mut sat_tree = SatTree::new();
        for clause in clauses {
            let tree = sat_tree.alloc_tree(clause);
            sat_tree.insert_tree(tree);
        }
        sat_tree
    }

    pub fn solve(&self) -> Option<Vec<isize>> {
        if self.root_op.is_none() {
            return None;
        }
        let mut at_tree_stack: Vec<(Vec<isize>, usize)> = Vec::new();
        let mut at_node_stack: Vec<(Vec<isize>, Node)> = Vec::new();
        at_tree_stack.push((Vec::new(), self.root_op.unwrap()));
        while let Some((fixed_lits, at_tree_id)) = at_tree_stack.pop() {
            let at_tree = self.tree_map.get(&at_tree_id).unwrap();
            println!("tree {}", at_tree_id);
            at_node_stack.push((Vec::new(), at_tree.root));
            while let Some((mut at_path, at_node)) = at_node_stack.pop() {
                println!("fixed {:?}", fixed_lits);
                println!("path {:?}", at_path);
                println!("{:?}", at_node);
                match at_node {
                    Node::Tree(at_tree_id2) => {
                        let mut fixed_lits2 = fixed_lits.clone();
                        fixed_lits2.append(&mut at_path);
                        fixed_lits2.sort_by(|a, b| a.abs().cmp(&b.abs()));
                        fixed_lits2.dedup();
                        at_tree_stack.push((fixed_lits2, at_tree_id2));
                    }
                    Node::Branch(at_branch_id) => {
                        let Branch {
                            id: _,
                            if_lit,
                            then,
                            else_,
                        } = *self.branch_map.get(&at_branch_id).unwrap();
                        let mut at_path2 = at_path.clone();
                        at_path.push(if_lit);
                        at_path2.push(-if_lit);
                        let dir_op = fixed_lits.iter().find_map(|lit| {
                            if *lit == if_lit {
                                Some(true)
                            } else if *lit == -if_lit {
                                Some(false)
                            } else {
                                None
                            }
                        });
                        if let Some(dir) = dir_op {
                            if dir {
                                at_node_stack.push((at_path, then));
                            } else {
                                at_node_stack.push((at_path2, else_));
                            }
                        } else {
                            at_node_stack.push((at_path, then));
                            at_node_stack.push((at_path2, else_));
                        }
                    }
                    Node::Leaf(value) => {
                        if value {
                            let mut path2 = fixed_lits.clone();
                            for x in &at_path {
                                path2.push(*x);
                            }
                            path2.sort_by(|a, b| a.abs().cmp(&b.abs()));
                            path2.dedup();
                            return Some(path2);
                        }
                    }
                }
            }
        }
        return None;
    }

    fn insert_tree(&mut self, tree_id: usize) {
        if self.root_op.is_none() {
            self.root_op = Some(tree_id);
            return;
        }
        let mut at_tree_stack: Vec<(Vec<isize>, usize)> = Vec::new();
        let mut at_node_stack: Vec<(Vec<isize>, Node)> = Vec::new();
        at_tree_stack.push((Vec::new(), self.root_op.unwrap()));
        while let Some((fixed_lits, at_tree_id)) = at_tree_stack.pop() {
            let at_tree = self.tree_map.get(&at_tree_id).unwrap();
            at_node_stack.push((Vec::new(), at_tree.root));
            while let Some((mut at_path, at_node)) = at_node_stack.pop() {
                match at_node {
                    Node::Tree(at_tree_id2) => {
                        if at_tree_id2 == tree_id {
                            continue;
                        }
                        let mut fixed_lits2 = fixed_lits.clone();
                        fixed_lits2.append(&mut at_path);
                        fixed_lits2.sort_by(|a, b| a.abs().cmp(&b.abs()));
                        fixed_lits2.dedup();
                        at_tree_stack.push((fixed_lits2, at_tree_id2));
                    }
                    Node::Branch(at_branch_id) => {
                        let Branch {
                            id: _,
                            if_lit,
                            then,
                            else_,
                        } = *self.branch_map.get(&at_branch_id).unwrap();
                        let mut at_path2 = at_path.clone();
                        at_path.push(if_lit);
                        at_path2.push(-if_lit);
                        let dir_op = fixed_lits.iter().find_map(|lit| {
                            if *lit == if_lit {
                                Some(true)
                            } else if *lit == -if_lit {
                                Some(false)
                            } else {
                                None
                            }
                        });
                        if let Some(dir) = dir_op {
                            if dir {
                                at_node_stack.push((at_path, then));
                            } else {
                                at_node_stack.push((at_path2, else_));
                            }
                        } else {
                            at_node_stack.push((at_path, then));
                            at_node_stack.push((at_path2, else_));
                        }
                    }
                    Node::Leaf(value) => {
                        if value {
                            let replacement;
                            let mut path2 = fixed_lits.clone();
                            for lit in &at_path {
                                path2.push(*lit);
                            }
                            if self.is_non_zero_path(tree_id, &path2) {
                                replacement = Node::Tree(tree_id);
                            } else {
                                replacement = Node::Leaf(false);
                            }
                            self.replace_node(at_tree_id, &at_path, replacement);
                        }
                    }
                }
            }
        }
    }

    fn is_non_zero_path(&self, tree_id: usize, path: &Vec<isize>) -> bool {
        let tree = self.tree_map.get(&tree_id).unwrap();
        let mut node_stack = Vec::new();
        node_stack.push(tree.root);
        while let Some(node) = node_stack.pop() {
            match node {
                Node::Tree(tree_id) => {
                    let tree = self.tree_map.get(&tree_id).unwrap();
                    node_stack.push(tree.root);
                }
                Node::Branch(branch_id) => {
                    let Branch {
                        id: _,
                        if_lit,
                        then,
                        else_,
                    } = *self.branch_map.get(&branch_id).unwrap();
                    let dir_op = path.iter().find_map(|lit| {
                        if *lit == if_lit {
                            Some(true)
                        } else if *lit == -if_lit {
                            Some(false)
                        } else {
                            None
                        }
                    });
                    if let Some(dir) = dir_op {
                        if dir {
                            node_stack.push(then);
                        } else {
                            node_stack.push(else_);
                        }
                    }
                }
                Node::Leaf(value) => {
                    if !value {
                        return false;
                    }
                }
            }
        }
        true
    }

    fn replace_node(&mut self, tree_id: usize, path: &Vec<isize>, node: Node) {
        let mut at_node;
        {
            let tree = self.tree_map.get_mut(&tree_id).unwrap();
            if path.is_empty() {
                tree.root = node;
                return;
            }
            at_node = tree.root;
        }
        let mut idx = 0;
        while idx < path.len() {
            match at_node {
                Node::Branch(branch_id) => {
                    let &mut Branch {
                        id: _,
                        if_lit,
                        ref mut then,
                        ref mut else_,
                    } = self.branch_map.get_mut(&branch_id).unwrap();
                    if if_lit == path[idx] {
                        if idx == path.len() - 1 {
                            *then = node;
                            return;
                        }
                        at_node = *then;
                    } else if if_lit == -path[idx] {
                        if idx == path.len() - 1 {
                            *else_ = node;
                            return;
                        }
                        at_node = *else_;
                    } else {
                        return;
                    }
                    idx += 1;
                }
                _ => {
                    return;
                }
            }
        }
    }

    fn alloc_tree(&mut self, clause: &Vec<isize>) -> usize {
        println!("{:?}", clause);
        let then_branch = Node::Leaf(true);
        let mut else_branch = Node::Leaf(false);
        for lit in clause.iter().rev() {
            let branch_id = self.alloc_branch(*lit, then_branch, else_branch);
            else_branch = Node::Branch(branch_id);
        }
        let id = self.next_id;
        self.next_id += 1;
        self.tree_map.insert(
            id,
            Tree {
                id,
                root: else_branch,
            },
        );
        id
    }

    fn alloc_branch(&mut self, lit: isize, then: Node, else_: Node) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        self.branch_map.insert(
            id,
            Branch {
                id,
                if_lit: lit,
                then,
                else_,
            },
        );
        id
    }
}

#[test]
fn test_sat_tree() {
    let clauses = vec![
        vec![1, 2, 3],
        vec![1, 2, -3],
        vec![1, -2, 3],
        vec![1, -2, -3],
        vec![-1, 2, 3],
        vec![-1, -2, 3],
        vec![-1, -2, -3],
    ];
    let sat = SatTree::from_clauses(&clauses);
    println!("{:?}", clauses);
    println!();
    println!("{:#?}", sat);
    println!();
    println!("{:?}", sat.solve());
}
