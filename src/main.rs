use num_bigint::BigInt;
use std::cmp::max;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::io::Write;
use std::ops::BitAnd;
use std::ops::BitAndAssign;
use std::rc::Rc;
use std::str::FromStr;

mod _1_in_all_sat;
mod _2sat;
mod _3sat;
mod circuit;
mod cnf;
mod density;
mod dimacs;
pub mod heuristic;
mod random;
mod sat;
mod sat_tree;
pub mod solver1;
pub mod solver2;
mod types;

pub use crate::_1_in_all_sat::_1InAllSat;
pub use crate::_2sat::_2Sat;
pub use crate::_3sat::_3Sat;
pub use crate::circuit::{Circuit, CircuitGate, CircuitVar};
pub use crate::cnf::CNF;
pub use crate::dimacs::parse_dimacs;
pub use crate::random::{Rand, Rng};
pub use crate::sat::Sat;
pub use crate::sat_tree::SatTree;
pub use crate::types::{Var,Lit,CnfClause,CnfFormula,DnfClause,DnfFormula};

const RSA_2048_STR: &str = "
        2519590847565789349402718324004839857142928212620403202777713783604366202070
        7595556264018525880784406918290641249515082189298559149176184502808489120072
        8449926873928072877767359714183472702618963750149718246911650776133798590957
        0009733045974880842840179742910064245869181719511874612151517265463228221686
        9987549182422433637259085141865462043576798423387184774447920739934236584823
        8242811981638150106748104516603773060562016196762561338441436038339044149526
        3443219011465754445417842402092461651572335077870774981712577246796292638635
        6373289912154831438167899885040445364023527381951378636564391212010397122822
        120720357";

#[derive(Clone)]
pub struct AD2 {
    pub f: Rc<dyn Fn(f64, f64) -> f64>,
    pub df_dx: Rc<dyn Fn(f64, f64) -> f64>,
    pub df_dy: Rc<dyn Fn(f64, f64) -> f64>,
}

impl AD2 {
    pub fn eval(&self, x: f64, y: f64) -> f64 {
        (self.f)(x, y)
    }

    pub fn eval_df_dx(&self, x: f64, y: f64) -> f64 {
        (self.df_dx)(x, y)
    }

    pub fn eval_df_dy(&self, x: f64, y: f64) -> f64 {
        (self.df_dy)(x, y)
    }

    pub fn compose(&self, arg1: AD2, arg2: AD2) -> AD2 {
        let f;
        let df_dx;
        let df_dy;
        {
            let self_f = self.f.clone();
            let arg1_f = arg1.f.clone();
            let arg2_f = arg2.f.clone();
            f = Rc::new(move |x: f64, y: f64| self_f(arg1_f(x, y), arg2_f(x, y)));
        }
        {
            let self_df_da = self.df_dx.clone();
            let self_df_db = self.df_dy.clone();
            let arg1_f = arg1.f.clone();
            let arg2_f = arg2.f.clone();
            let arg1_df_dx = arg1.df_dx.clone();
            let arg2_df_dx = arg2.df_dx.clone();
            df_dx = Rc::new(move |x: f64, y: f64| {
                let a = arg1_f(x, y);
                let b = arg2_f(x, y);
                self_df_da(a, b) * arg1_df_dx(x, y) + self_df_db(a, b) * arg2_df_dx(x, y)
            });
        }
        {
            let self_df_da = self.df_dx.clone();
            let self_df_db = self.df_dy.clone();
            let arg1_f = arg1.f.clone();
            let arg2_f = arg2.f.clone();
            let arg1_df_dy = arg1.df_dy.clone();
            let arg2_df_dy = arg2.df_dy.clone();
            df_dy = Rc::new(move |x: f64, y: f64| {
                let a = arg1_f(x, y);
                let b = arg2_f(x, y);
                self_df_da(a, b) * arg1_df_dy(x, y) + self_df_db(a, b) * arg2_df_dy(x, y)
            });
        }
        AD2 { f, df_dx, df_dy }
    }

    pub fn solve(&self) -> AD2 {
        let f;
        let df_dx;
        let df_dy;
        {
            let self_f = self.f.clone();
            f = Rc::new(move |x: f64, y: f64| {
                let z = self_f(x, y) - 1.0;
                z * z
            });
        }
        {
            let self_f = self.f.clone();
            let self_df_dx = self.df_dx.clone();
            df_dx = Rc::new(move |x: f64, y: f64| 2.0 * (self_f(x, y) - 1.0) * self_df_dx(x, y));
        }
        {
            let self_f = self.f.clone();
            let self_df_dy = self.df_dy.clone();
            df_dy = Rc::new(move |x: f64, y: f64| 2.0 * (self_f(x, y) - 1.0) * self_df_dy(x, y));
        }
        AD2 { f, df_dx, df_dy }
    }

    pub fn solve_many(ad2s: Vec<AD2>) -> AD2 {
        let ad2s = Rc::new(ad2s);
        let f;
        let df_dx;
        let df_dy;
        {
            let ad2s = ad2s.clone();
            f = Rc::new(move |x: f64, y: f64| {
                let mut sum: f64 = 0.0;
                let ad2s: &Vec<AD2> = &*ad2s;
                for ad2 in ad2s {
                    let z = ad2.eval(x, y) - 1.0;
                    sum += z * z;
                }
                sum
            });
        }
        {
            let ad2s = ad2s.clone();
            df_dx = Rc::new(move |x: f64, y: f64| {
                let mut sum: f64 = 0.0;
                let ad2s: &Vec<AD2> = &*ad2s;
                for ad2 in ad2s {
                    sum += 2.0 * (ad2.eval(x, y) - 1.0) * ad2.eval_df_dx(x, y);
                }
                sum
            });
        }
        {
            let ad2s = ad2s.clone();
            df_dy = Rc::new(move |x: f64, y: f64| {
                let mut sum: f64 = 0.0;
                let ad2s: &Vec<AD2> = &*ad2s;
                for ad2 in ad2s {
                    sum += 2.0 * (ad2.eval(x, y) - 1.0) * ad2.eval_df_dy(x, y);
                }
                sum
            });
        }
        AD2 { f, df_dx, df_dy }
    }

    pub fn const_(a: f64) -> AD2 {
        AD2 {
            f: Rc::new(move |_x: f64, _y: f64| a),
            df_dx: Rc::new(|_x: f64, _y: f64| 0.0),
            df_dy: Rc::new(|_x: f64, _y: f64| 0.0),
        }
    }

    pub fn x() -> AD2 {
        AD2 {
            f: Rc::new(|x: f64, _y: f64| x),
            df_dx: Rc::new(|_x: f64, _y: f64| 1.0),
            df_dy: Rc::new(|_x: f64, _y: f64| 0.0),
        }
    }

    pub fn y() -> AD2 {
        AD2 {
            f: Rc::new(|_x: f64, y: f64| y),
            df_dx: Rc::new(|_x: f64, _y: f64| 0.0),
            df_dy: Rc::new(|_x: f64, _y: f64| 1.0),
        }
    }

    pub fn or(self, rhs: AD2) -> AD2 {
        AD2::or_().compose(self, rhs)
    }

    pub fn and(self, rhs: AD2) -> AD2 {
        AD2::and_().compose(self, rhs)
    }

    pub fn xor(self, rhs: AD2) -> AD2 {
        AD2::xor_().compose(self, rhs)
    }

    pub fn or_() -> AD2 {
        AD2 {
            f: Rc::new(|x: f64, y: f64| 0.5 * x + 0.5 * y - 0.5 * x * y + 0.5),
            df_dx: Rc::new(|_x: f64, y: f64| 0.5 - 0.5 * y),
            df_dy: Rc::new(|x: f64, _y: f64| 0.5 - 0.5 * x),
        }
    }

    pub fn and_() -> AD2 {
        AD2 {
            f: Rc::new(|x: f64, y: f64| 0.5 * x + 0.5 * y + 0.5 * x * y - 0.5),
            df_dx: Rc::new(|_x: f64, y: f64| 0.5 + 0.5 * y),
            df_dy: Rc::new(|x: f64, _y: f64| 0.5 + 0.5 * x),
        }
    }

    pub fn xor_() -> AD2 {
        AD2 {
            f: Rc::new(|x: f64, y: f64| -x * y),
            df_dx: Rc::new(|_x: f64, y: f64| -y),
            df_dy: Rc::new(|x: f64, _y: f64| -x),
        }
    }

    pub fn not(&self) -> AD2 {
        let self_f = self.f.clone();
        let self_df_dx = self.df_dx.clone();
        let self_df_dy = self.df_dy.clone();
        AD2 {
            f: Rc::new(move |x: f64, y: f64| -self_f(x, y)),
            df_dx: Rc::new(move |x: f64, y: f64| -self_df_dx(x, y)),
            df_dy: Rc::new(move |x: f64, y: f64| -self_df_dy(x, y)),
        }
    }
}

#[derive(Clone)]
pub enum Expr {
    Var(String),
    Const(f64),
    Add(Box<Expr>, Box<Expr>),
    Mult(Box<Expr>, Box<Expr>),
    Squared(Box<Expr>),
}

impl Expr {
    pub fn var(name: String) -> Expr {
        Expr::Var(name)
    }

    pub fn const_(a: f64) -> Expr {
        Expr::Const(a)
    }

    pub fn add(self, rhs: Expr) -> Expr {
        Expr::Add(Box::new(self), Box::new(rhs))
    }

    pub fn mult(self, rhs: Expr) -> Expr {
        Expr::Mult(Box::new(self), Box::new(rhs))
    }

    pub fn squared(self) -> Expr {
        Expr::Squared(Box::new(self))
    }

    pub fn true_() -> Expr {
        Expr::const_(1.0)
    }

    pub fn false_() -> Expr {
        Expr::const_(-1.0)
    }

    pub fn or(self, rhs: Expr) -> Expr {
        let x = self;
        let y = rhs;
        x.clone()
            .mult(Expr::const_(0.5))
            .add(y.clone().mult(Expr::const_(0.5)))
            .add(x.mult(y).mult(Expr::const_(-0.5)))
            .add(Expr::const_(0.5))
    }

    pub fn and(self, rhs: Expr) -> Expr {
        let x = self;
        let y = rhs;
        x.clone()
            .mult(Expr::const_(0.5))
            .add(y.clone().mult(Expr::const_(0.5)))
            .add(x.mult(y).mult(Expr::const_(0.5)))
            .add(Expr::const_(-0.5))
    }

    pub fn xor(self, rhs: Expr) -> Expr {
        let x = self;
        let y = rhs;
        x.mult(y).mult(Expr::const_(-1.0))
    }

    pub fn not(self) -> Expr {
        self.mult(Expr::const_(-1.0))
    }

    pub fn dexp_dvar(&self, name: &String) -> Expr {
        match self {
            &Expr::Var(ref name2) => {
                if name.cmp(name2) == std::cmp::Ordering::Equal {
                    Expr::const_(1.0)
                } else {
                    Expr::const_(0.0)
                }
            }
            &Expr::Const(_) => Expr::const_(0.0),
            &Expr::Add(ref lhs, ref rhs) => lhs.dexp_dvar(name).add(rhs.dexp_dvar(name)),
            &Expr::Mult(ref lhs, ref rhs) => {
                let lhs: Expr = (lhs as &Expr).clone();
                let rhs: Expr = (rhs as &Expr).clone();
                let dlhs_dvar = lhs.dexp_dvar(name);
                let drhs_dvar = rhs.dexp_dvar(name);
                dlhs_dvar.mult(rhs).add(lhs.mult(drhs_dvar))
            }
            &Expr::Squared(ref expr) => {
                let x = (expr as &Expr).clone();
                let dx_dvar = x.dexp_dvar(name);
                x.mult(Expr::const_(2.0)).mult(dx_dvar)
            }
        }
    }

    pub fn extract_vars(&self) -> Vec<String> {
        fn extract_vars2(expr: &Expr, vars: &mut HashSet<String>) {
            match expr {
                &Expr::Var(ref name) => {
                    vars.insert(name.clone());
                }
                &Expr::Const(_) => {}
                &Expr::Add(ref lhs, ref rhs) => {
                    extract_vars2(lhs, vars);
                    extract_vars2(rhs, vars);
                }
                &Expr::Mult(ref lhs, ref rhs) => {
                    extract_vars2(lhs, vars);
                    extract_vars2(rhs, vars);
                }
                &Expr::Squared(ref x) => {
                    extract_vars2(x, vars);
                }
            }
        };
        let mut vars = HashSet::new();
        extract_vars2(self, &mut vars);
        vars.drain().collect()
    }

    pub fn eval(&self, var_map: &mut HashMap<String, f64>) -> Option<f64> {
        match self {
            &Expr::Var(ref name) => var_map.get(name).map(|x| *x),
            &Expr::Const(ref a) => Some(a.clone()),
            &Expr::Add(ref lhs, ref rhs) => {
                let x_op = lhs.eval(var_map);
                let y_op = rhs.eval(var_map);
                if let Some(x) = x_op {
                    if let Some(y) = y_op {
                        return Some(x + y);
                    }
                }
                None
            }
            &Expr::Mult(ref lhs, ref rhs) => {
                let x_op = lhs.eval(var_map);
                let y_op = rhs.eval(var_map);
                if let Some(x) = x_op {
                    if let Some(y) = y_op {
                        return Some(x * y);
                    }
                }
                None
            }
            &Expr::Squared(ref expr) => {
                let x_op = expr.eval(var_map);
                if let Some(x) = x_op {
                    return Some(x * x);
                }
                None
            }
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            &Expr::Var(ref name) => {
                write!(formatter, "{}", name)?;
            }
            &Expr::Const(ref a) => {
                write!(formatter, "{}", a)?;
            }
            &Expr::Add(ref lhs, ref rhs) => {
                write!(formatter, "({} + {})", lhs, rhs)?;
            }
            &Expr::Mult(ref lhs, ref rhs) => {
                write!(formatter, "({} * {})", lhs, rhs)?;
            }
            &Expr::Squared(ref x) => {
                write!(formatter, "pow({}, 2)", x)?;
            }
        }
        Ok(())
    }
}

#[derive(Clone)]
pub enum BoolExpr {
    Var(char, usize),
    And(Box<BoolExpr>, Box<BoolExpr>),
    Or(Box<BoolExpr>, Box<BoolExpr>),
    Not(Box<BoolExpr>),
}

pub struct AdderResult {
    pub carry: BoolExpr,
    pub out: BoolExpr,
}

impl BoolExpr {
    pub fn var(letter: char, subscript: usize) -> BoolExpr {
        BoolExpr::Var(letter, subscript)
    }

    pub fn and(self, rhs: BoolExpr) -> BoolExpr {
        BoolExpr::And(Box::new(self), Box::new(rhs))
    }

    pub fn or(self, rhs: BoolExpr) -> BoolExpr {
        BoolExpr::Or(Box::new(self), Box::new(rhs))
    }

    pub fn not(self) -> BoolExpr {
        BoolExpr::Not(Box::new(self))
    }

    pub fn xor(self, rhs: BoolExpr) -> BoolExpr {
        let lhs = self;
        let lhs2 = lhs.clone();
        let rhs2 = rhs.clone();
        lhs.not().and(rhs).or(lhs2.and(rhs2.not()))
    }

    pub fn half_adder(bit1: BoolExpr, bit2: BoolExpr) -> AdderResult {
        let bit12 = bit1.clone();
        let bit22 = bit2.clone();
        AdderResult {
            out: bit1.xor(bit2),
            carry: bit12.and(bit22),
        }
    }

    pub fn full_adder(bit1: BoolExpr, bit2: BoolExpr, carry: BoolExpr) -> AdderResult {
        let r1 = BoolExpr::half_adder(bit1, bit2);
        let r2 = BoolExpr::half_adder(r1.out, carry);
        AdderResult {
            out: r2.out,
            carry: r1.carry.or(r2.carry),
        }
    }

    pub fn adder(lhs_bits: Vec<BoolExpr>, rhs_bits: Vec<BoolExpr>) -> Vec<BoolExpr> {
        let n = max(lhs_bits.len(), rhs_bits.len());
        if n == 0 {
            return Vec::new();
        }
        let mut result = Vec::new();
        let mut carry;
        {
            let lhs = lhs_bits[0].clone();
            let rhs = rhs_bits[0].clone();
            let AdderResult { out, carry: carry2 } = BoolExpr::half_adder(lhs, rhs);
            carry = carry2;
            result.push(out);
        }
        for i in 1..n {
            let lhs = lhs_bits[i].clone();
            let rhs = rhs_bits[i].clone();
            let AdderResult { out, carry: carry2 } = BoolExpr::full_adder(lhs, rhs, carry.clone());
            carry = carry2;
            result.push(out);
        }
        for i in n..lhs_bits.len() {
            let lhs = lhs_bits[i].clone();
            let AdderResult { out, carry: carry2 } = BoolExpr::half_adder(lhs, carry.clone());
            carry = carry2;
            result.push(out);
        }
        for i in n..rhs_bits.len() {
            let rhs = rhs_bits[i].clone();
            let AdderResult { out, carry: carry2 } = BoolExpr::half_adder(rhs, carry.clone());
            carry = carry2;
            result.push(out);
        }
        result.push(carry);
        result.reverse();
        result
    }

    pub fn multiplier(mut lhs_bits: Vec<BoolExpr>, mut rhs_bits: Vec<BoolExpr>) -> Vec<BoolExpr> {
        lhs_bits.reverse();
        rhs_bits.reverse();
        let mut result = Vec::new();
        let out_pin_count;
        {
            let n = lhs_bits.len() * rhs_bits.len();
            if n == 1 {
                out_pin_count = 1;
            } else {
                out_pin_count = 2 * n;
            }
        }
        if out_pin_count == 0 {
            return result;
        }
        result.push(lhs_bits[0].clone().and(rhs_bits[0].clone()));
        let mut s: Vec<BoolExpr> = Vec::new();
        let mut next_s: Vec<BoolExpr> = Vec::new();
        for j in 1..lhs_bits.len() {
            s.push(lhs_bits[j].clone().and(rhs_bits[0].clone()));
        }
        let mut last_row_carry_op: Option<BoolExpr> = None;
        for i in 1..rhs_bits.len() {
            let mut c;
            {
                let AdderResult { out: x, carry: rc } =
                    BoolExpr::half_adder(lhs_bits[0].clone(), s[0].clone());
                result.push(x.clone());
                next_s.push(x);
                c = rc;
            }
            for j in 1..s.len() - 1 {
                let AdderResult { out: x, carry: rc } = BoolExpr::full_adder(
                    s[j].clone(),
                    lhs_bits[j].clone().and(rhs_bits[i].clone()),
                    c,
                );
                c = rc;
                next_s.push(x);
            }
            let next_last_row_carry;
            match &last_row_carry_op {
                &None => {
                    let AdderResult { out: x, carry: rc } = BoolExpr::half_adder(
                        c,
                        lhs_bits[s.len() - 1].clone().and(rhs_bits[i].clone()),
                    );
                    next_last_row_carry = rc;
                    next_s.push(x);
                }
                &Some(ref last_row_carry) => {
                    let AdderResult { out: x, carry: rc } = BoolExpr::full_adder(
                        last_row_carry.clone(),
                        c,
                        lhs_bits[s.len() - 1].clone().and(rhs_bits[i].clone()),
                    );
                    next_last_row_carry = rc;
                    next_s.push(x);
                }
            }
            last_row_carry_op = Some(next_last_row_carry);
            std::mem::swap(&mut s, &mut next_s);
            next_s.clear();
        }
        for x in s {
            result.push(x);
        }
        if let Some(last_row_carry) = last_row_carry_op {
            result.push(last_row_carry);
        }
        result.reverse();
        result
    }
}

impl fmt::Display for BoolExpr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            &BoolExpr::Var(ref letter, ref subscript) => {
                write!(formatter, "{}[{}]", letter, subscript)?;
            }
            &BoolExpr::And(ref lhs, ref rhs) => {
                write!(formatter, "({} & {})", lhs, rhs)?;
            }
            &BoolExpr::Or(ref lhs, ref rhs) => {
                write!(formatter, "({} | {})", lhs, rhs)?;
            }
            &BoolExpr::Not(ref expr) => {
                write!(formatter, "!({})", expr)?;
            }
        }
        Ok(())
    }
}

pub struct CircuitEvaluator {
    gates: Vec<CircuitGate>,
    var_names: HashMap<usize, String>,
}

impl CircuitEvaluator {
    pub fn new(circuit: &Circuit) -> CircuitEvaluator {
        // Circuit is already in DAG, so skip topological sort.
        /*
        let mut gate_map: HashMap<usize, CircuitGate> = HashMap::new();
        let mut node_edges_map: HashMap<usize, Vec<usize>> = HashMap::new();
        let mut out_nodes_map: HashMap<usize, Vec<usize>> = HashMap::new();
        let mut in_edges: Vec<usize> = Vec::new();
        for gate in &circuit.gates {
            let gate_name: usize;
            in_edges.clear();
            match gate {
                &CircuitGate::And(ref in1, ref in2, ref out) => {
                    in_edges.push(in1.id);
                    in_edges.push(in2.id);
                    gate_name = out.id;
                }
                &CircuitGate::Or(ref in1, ref in2, ref out) => {
                    in_edges.push(in1.id);
                    in_edges.push(in2.id);
                    gate_name = out.id;
                }
                &CircuitGate::Not(ref in_, ref out) => {
                    in_edges.push(in_.id);
                    gate_name = out.id;
                }
                &CircuitGate::Xor(ref in1, ref in2, ref out) => {
                    in_edges.push(in1.id);
                    in_edges.push(in2.id);
                    gate_name = out.id;
                }
                &CircuitGate::Imp(ref in1, ref in2, ref out) => {
                    in_edges.push(in1.id);
                    in_edges.push(in2.id);
                    gate_name = out.id;
                }
                &CircuitGate::Eq(ref in1, ref in2, ref out) => {
                    in_edges.push(in1.id);
                    in_edges.push(in2.id);
                    gate_name = out.id;
                }
            }
            for in_edge in &in_edges {
                gate_input_var_set.insert(*in_edge);
            }
            gate_output_var_set.insert(gate_name);
            gate_map.insert(gate_name, gate.clone());
            for in_edge in &in_edges {
                let found;
                if let Some(ref mut nodes) = out_nodes_map.get_mut(in_edge) {
                    nodes.push(gate_name);
                    found = true;
                } else {
                    found = false;
                }
                if !found {
                    out_nodes_map.insert(*in_edge, vec![gate_name]);
                }
            }
            let found;
            {
                let edges_op = node_edges_map.get_mut(&gate_name);
                if let Some(edges) = edges_op {
                    edges.append(&mut in_edges);
                    found = true;
                } else {
                    found = false;
                }
            }
            if !found {
                node_edges_map.insert(gate_name, in_edges.clone());
            }
        }
        let mut stack = Vec::new();
        for (node, edges) in &mut node_edges_map {
            edges.retain(|e| gate_map.get(e).is_some());
            if edges.is_empty() {
                stack.push(*node);
            }
        }
        let mut gates: Vec<CircuitGate> = Vec::new();
        loop {
            let gate_name_op = stack.pop();
            if let Some(gate_name) = gate_name_op {
                let gate = gate_map.get(&gate_name).unwrap().clone();
                let nexts_op = out_nodes_map.get(&gate_name);
                if let Some(nexts) = nexts_op {
                    for next in nexts {
                        if let Some(edges) = node_edges_map.get_mut(&next) {
                            edges.retain(|edge| *edge != gate_name);
                            if edges.is_empty() {
                                stack.push(*next);
                            }
                        }
                    }
                }
                gates.push(gate.clone());
            } else {
                break;
            }
        }
        CircuitEvaluator {
            gates,
            var_names: circuit.var_names.clone(),
        }
        */
        CircuitEvaluator {
            gates: circuit.gates.clone(),
            var_names: circuit.var_names.clone(),
        }
    }

    fn id_to_name(&self, id: &usize) -> &String {
        self.var_names.get(id).unwrap()
    }

    pub fn run(&self, var_map: &mut HashMap<String, bool>) {
        fn get_var(
            circuit_eval: &CircuitEvaluator,
            var_map: &HashMap<String, bool>,
            var: &CircuitVar,
        ) -> bool {
            let var_name = circuit_eval.id_to_name(&var.id);
            *var_map.get(var_name).unwrap()
        }
        fn set_var(
            circuit_eval: &CircuitEvaluator,
            var_map: &mut HashMap<String, bool>,
            var: &CircuitVar,
            val: bool,
        ) {
            let var_name = circuit_eval.id_to_name(&var.id);
            if let Some(x) = var_map.get_mut(var_name) {
                *x = val;
                return;
            }
            var_map.insert(var_name.clone(), val);
        }
        for gate in &self.gates {
            match gate {
                &CircuitGate::And(ref in1, ref in2, ref out) => {
                    let x = get_var(self, var_map, in1);
                    let y = get_var(self, var_map, in2);
                    set_var(self, var_map, out, x && y);
                }
                &CircuitGate::Or(ref in1, ref in2, ref out) => {
                    let x = get_var(self, var_map, in1);
                    let y = get_var(self, var_map, in2);
                    set_var(self, var_map, out, x || y);
                }
                &CircuitGate::Not(ref in_, ref out) => {
                    let x = get_var(self, var_map, in_);
                    set_var(self, var_map, out, !x);
                }
                &CircuitGate::Xor(ref in1, ref in2, ref out) => {
                    let x = get_var(self, var_map, in1);
                    let y = get_var(self, var_map, in2);
                    set_var(self, var_map, out, x ^ y);
                }
                &CircuitGate::Imp(ref in1, ref in2, ref out) => {
                    let x = get_var(self, var_map, in1);
                    let y = get_var(self, var_map, in2);
                    set_var(self, var_map, out, !x || y);
                }
                &CircuitGate::Eq(ref in1, ref in2, ref out) => {
                    let x = get_var(self, var_map, in1);
                    let y = get_var(self, var_map, in2);
                    set_var(self, var_map, out, x == y);
                }
            }
        }
    }

    pub fn run_sparse_tt(&self, var_map: &mut HashMap<String, SparseTT>) {
        fn get_var(
            circuit_eval: &CircuitEvaluator,
            var_map: &HashMap<String, SparseTT>,
            var: &CircuitVar,
        ) -> SparseTT {
            let var_name = circuit_eval.id_to_name(&var.id);
            var_map.get(var_name).unwrap().clone()
        }
        fn set_var(
            circuit_eval: &CircuitEvaluator,
            var_map: &mut HashMap<String, SparseTT>,
            var: &CircuitVar,
            val: SparseTT,
        ) {
            let var_name = circuit_eval.id_to_name(&var.id);
            if let Some(x) = var_map.get_mut(var_name) {
                *x = val;
                return;
            }
            var_map.insert(var_name.clone(), val);
        }
        for gate in &self.gates {
            match gate {
                &CircuitGate::And(ref in1, ref in2, ref out) => {
                    let x = get_var(self, var_map, in1);
                    let y = get_var(self, var_map, in2);
                    set_var(self, var_map, out, x.and(y).simplify());
                }
                &CircuitGate::Or(ref in1, ref in2, ref out) => {
                    let x = get_var(self, var_map, in1);
                    let y = get_var(self, var_map, in2);
                    set_var(self, var_map, out, x.or(y).simplify());
                }
                &CircuitGate::Not(ref in_, ref out) => {
                    let x = get_var(self, var_map, in_);
                    set_var(self, var_map, out, x.not());
                }
                &CircuitGate::Xor(ref in1, ref in2, ref out) => {
                    let x = get_var(self, var_map, in1);
                    let y = get_var(self, var_map, in2);
                    set_var(self, var_map, out, x.xor(y).simplify());
                }
                &CircuitGate::Imp(ref in1, ref in2, ref out) => {
                    let x = get_var(self, var_map, in1);
                    let y = get_var(self, var_map, in2);
                    set_var(self, var_map, out, x.imp(y).simplify());
                }
                &CircuitGate::Eq(ref in1, ref in2, ref out) => {
                    let x = get_var(self, var_map, in1);
                    let y = get_var(self, var_map, in2);
                    set_var(self, var_map, out, x.eq(y).simplify());
                }
            }
        }
    }

    pub fn run_numeric(&self, dvar_map: &mut HashMap<usize, (f64, Vec<f64>)>) {
        fn read_var(
            dvar_map: &mut HashMap<usize, (f64, Vec<f64>)>,
            var: usize,
            out: &mut (f64, Vec<f64>),
        ) {
            out.0 = 0.0;
            if let Some(x) = dvar_map.get(&var) {
                out.0 = x.0;
                let mut i = 0;
                for z in &x.1 {
                    if out.1.len() <= i {
                        out.1.push(*z);
                    } else {
                        out.1[i] = *z;
                    }
                    i += 1;
                }
                return;
            }
        }
        fn write_var(
            dvar_map: &mut HashMap<usize, (f64, Vec<f64>)>,
            var: usize,
            out: &(f64, Vec<f64>),
        ) {
            let found;
            if let Some(x) = dvar_map.get_mut(&var) {
                found = true;
                x.0 = out.0;
                let mut i = 0;
                for z in &out.1 {
                    if out.1.len() <= i {
                        x.1.push(*z);
                    } else {
                        x.1[i] = *z;
                    }
                    i += 1;
                }
            } else {
                found = false;
            }
            if !found {
                dvar_map.insert(var, out.clone());
            }
        }
        let mut in1_var: (f64, Vec<f64>) = (0.0, Vec::new());
        let mut in2_var: (f64, Vec<f64>) = (0.0, Vec::new());
        let mut out_var: (f64, Vec<f64>) = (0.0, Vec::new());
        for gate in &self.gates {
            match gate {
                &CircuitGate::And(ref in1, ref in2, ref out) => {
                    read_var(dvar_map, in1.id, &mut in1_var);
                    read_var(dvar_map, in2.id, &mut in2_var);
                    let x = in1_var.0;
                    let y = in2_var.0;
                    let z = x * y;
                    out_var.0 = z;
                    let dout_var_din1_var = y;
                    let dout_var_din2_var = x;
                    out_var.1.clear();
                    in1_var
                        .1
                        .iter()
                        .zip(in2_var.1.iter())
                        .map(|(din1_dx, din2_dx)| {
                            dout_var_din1_var * *din1_dx + dout_var_din2_var * *din2_dx
                        })
                        .for_each(|x| out_var.1.push(x));
                    write_var(dvar_map, out.id, &out_var);
                }
                &CircuitGate::Or(ref in1, ref in2, ref out) => {
                    read_var(dvar_map, in1.id, &mut in1_var);
                    read_var(dvar_map, in2.id, &mut in2_var);
                    out_var.0 = in1_var.0 * in2_var.0;
                    out_var.1.clear();
                    in1_var
                        .1
                        .iter()
                        .zip(in2_var.1.iter())
                        .map(|(din1_dx, din2_dx)| in2_var.0 * *din1_dx + in1_var.0 * *din2_dx)
                        .for_each(|x| out_var.1.push(x));
                    write_var(dvar_map, out.id, &out_var);
                }
                &CircuitGate::Not(ref in_, ref out) => {
                    read_var(dvar_map, in_.id, &mut in1_var);
                    out_var.0 = 1.0 - in1_var.0;
                    let dout_var_din1_var = -1.0;
                    out_var.1.clear();
                    in1_var
                        .1
                        .iter()
                        .map(|din1_dx| dout_var_din1_var * *din1_dx)
                        .for_each(|x| out_var.1.push(x));
                    write_var(dvar_map, out.id, &out_var);
                }
                &CircuitGate::Xor(ref in1, ref in2, ref out) => {
                    read_var(dvar_map, in1.id, &mut in1_var);
                    read_var(dvar_map, in2.id, &mut in2_var);
                    let x = in1_var.0;
                    let y = in2_var.0;
                    let z = x + y - 2.0 * x * y;
                    out_var.0 = z;
                    let dout_var_din1_var = 1.0 - 2.0 * y;
                    let dout_var_din2_var = 1.0 - 2.0 * x;
                    out_var.1.clear();
                    in1_var
                        .1
                        .iter()
                        .zip(in2_var.1.iter())
                        .map(|(din1_dx, din2_dx)| {
                            dout_var_din1_var * *din1_dx + dout_var_din2_var * *din2_dx
                        })
                        .for_each(|x| out_var.1.push(x));
                    write_var(dvar_map, out.id, &out_var);
                }
                &CircuitGate::Imp(ref in1, ref in2, ref out) => {
                    read_var(dvar_map, in1.id, &mut in1_var);
                    read_var(dvar_map, in2.id, &mut in2_var);
                    out_var.0 = (1.0 - in1_var.0) * in2_var.0;
                    let dout_var_din1_var = -in2_var.0;
                    let dout_var_din2_var = -in1_var.0;
                    out_var.1.clear();
                    in1_var
                        .1
                        .iter()
                        .zip(in2_var.1.iter())
                        .map(|(din1_dx, din2_dx)| {
                            dout_var_din1_var * *din1_dx + dout_var_din2_var * *din2_dx
                        })
                        .for_each(|x| out_var.1.push(x));
                    write_var(dvar_map, out.id, &out_var);
                }
                &CircuitGate::Eq(ref in1, ref in2, ref out) => {
                    read_var(dvar_map, in1.id, &mut in1_var);
                    read_var(dvar_map, in2.id, &mut in2_var);
                    out_var.0 = ((1.0 - in1_var.0) + (1.0 - in2_var.0)) * (in1_var.0 + in2_var.0);
                    let dout_var_din1_var =
                        ((1.0 - in1_var.0) + (1.0 - in2_var.0)) + (in1_var.0 + in2_var.0) * -1.0;
                    let dout_var_din2_var =
                        ((1.0 - in1_var.0) + (1.0 - in2_var.0)) + (in1_var.0 + in2_var.0) * -1.0;
                    out_var.1.clear();
                    in1_var
                        .1
                        .iter()
                        .zip(in2_var.1.iter())
                        .map(|(din1_dx, din2_dx)| {
                            dout_var_din1_var * *din1_dx + dout_var_din2_var * *din2_dx
                        })
                        .for_each(|x| out_var.1.push(x));
                    write_var(dvar_map, out.id, &out_var);
                }
            }
        }
    }
}

pub fn clamp01(x: f64) -> f64 {
    if x < 0.0 {
        0.0
    } else if x > 1.0 {
        1.0
    } else {
        x
    }
}

pub fn clamp(x: f64) -> f64 {
    if x < -1.0 {
        -1.0
    } else if x > 1.0 {
        1.0
    } else {
        x
    }
}

pub fn sigmoid(x: f64) -> f64 {
    1.0 / (1.0 + (-x).exp())
}

pub fn d_sigmoid(x: f64) -> f64 {
    sigmoid(x) * (1.0 - sigmoid(x))
}

// Algebraic Normal Form. E.g. A xor B xor (A and B)
#[derive(Clone, PartialEq, Eq)]
pub struct Anf {
    pub terms: Vec<Vec<AnfAtom>>,
}

impl Anf {
    pub fn from_terms(terms: Vec<Vec<AnfAtom>>) -> Anf {
        Anf { terms }
    }

    pub fn true_() -> Anf {
        Anf {
            terms: vec![vec![AnfAtom::True]],
        }
    }

    pub fn var(name: String) -> Anf {
        Anf {
            terms: vec![vec![AnfAtom::Var(name)]],
        }
    }

    pub fn and(self, rhs: Anf) -> Anf {
        // (a xor b xor c)(d xor e)
        // ad xor ae xor bd xor be xor cd xor ce
        let terms = self
            .terms
            .iter()
            .flat_map(|lhs_term| {
                let lhs_term = lhs_term.clone();
                rhs.terms.iter().map(move |rhs_term| {
                    let mut combined = lhs_term.clone();
                    for rhs_atom in rhs_term {
                        combined.push(rhs_atom.clone());
                    }
                    combined.sort();
                    combined.dedup();
                    combined
                })
            })
            .collect();
        Anf { terms }.simplify()
    }

    pub fn or(self, rhs: Anf) -> Anf {
        // rule: X + Y = X xor Y xor XY
        let self2 = self.clone();
        let rhs2 = rhs.clone();
        self.xor(rhs).xor(self2.and(rhs2))
    }

    pub fn not(self) -> Anf {
        // rule: !X = X xor 1
        self.xor(Anf::true_())
    }

    pub fn xor(mut self, mut rhs: Anf) -> Anf {
        self.terms.append(&mut rhs.terms);
        self.simplify()
    }

    pub fn imp(self, rhs: Anf) -> Anf {
        self.not().or(rhs)
    }

    pub fn eq(self, rhs: Anf) -> Anf {
        self.xor(rhs).not()
    }

    pub fn simplify(mut self) -> Anf {
        for term in &mut self.terms {
            Anf::simplify_term(term);
        }
        let mut term_count_map: HashMap<Vec<AnfAtom>, u32> = HashMap::new();
        for term in &self.terms {
            let found;
            if let Some(count) = term_count_map.get_mut(term) {
                found = true;
                *count += 1;
            } else {
                found = false;
            }
            if !found {
                term_count_map.insert(term.clone(), 1);
            }
        }
        self.terms.clear();
        for (term, count) in term_count_map {
            if (count & 1) == 1 {
                self.terms.push(term);
            }
        }
        self.terms.sort();
        self
    }

    fn simplify_term(term: &mut Vec<AnfAtom>) {
        term.sort();
        term.dedup();
        if term.len() > 1 {
            term.retain(|atom| *atom != AnfAtom::True);
        }
    }
}

impl fmt::Display for Anf {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first_xor = true;
        writeln!(formatter, "Anf [")?;
        for ands in &self.terms {
            if first_xor {
                first_xor = false;
            } else {
                write!(formatter, ",")?;
            }
            let mut first_and = true;
            write!(formatter, "{{")?;
            for atom in ands {
                if first_and {
                    first_and = false;
                } else {
                    write!(formatter, ",")?;
                }
                match atom {
                    &AnfAtom::True => {
                        write!(formatter, "1")?;
                    }
                    &AnfAtom::Var(ref name) => {
                        write!(formatter, "{}", name)?;
                    }
                }
            }
            write!(formatter, "}}")?;
        }
        writeln!(formatter)?;
        Ok(())
    }
}

#[derive(Clone, PartialOrd, PartialEq, Ord, Eq, Hash)]
pub enum AnfAtom {
    True,
    Var(String),
}

#[derive(Clone)]
pub struct SparseTTContext {
    variable_name_map: HashMap<usize, String>,
    variable_id_map: HashMap<String, usize>,
    next_var_id: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SparseTT {
    Branch {
        variable: usize,
        false_path: Box<SparseTT>,
        true_path: Box<SparseTT>,
    },
    Leaf {
        value: bool,
    },
}

#[derive(Clone, Debug, Copy, PartialEq, Eq, Hash)]
pub struct SparseTTVar {
    id: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SparseTTLiteral {
    var: SparseTTVar,
    not: bool,
}

impl SparseTTContext {
    pub fn new() -> SparseTTContext {
        SparseTTContext {
            variable_name_map: HashMap::new(),
            variable_id_map: HashMap::new(),
            next_var_id: 0,
        }
    }

    pub fn alloc_var<NAME: ToString>(&mut self, name: NAME) -> SparseTTVar {
        let id = self.next_var_id;
        self.next_var_id += 1;
        self.variable_name_map.insert(id, name.to_string());
        self.variable_id_map.insert(name.to_string(), id);
        SparseTTVar { id }
    }

    pub fn var<NAME: ToString>(&mut self, name: NAME) -> SparseTTVar {
        if let Some(id) = self.variable_id_map.get(&name.to_string()) {
            return SparseTTVar { id: *id };
        }
        self.alloc_var(name)
    }
}

impl SparseTT {
    pub fn from_cnf(ctx: &mut SparseTTContext, cnf: &CNF) -> SparseTT {
        let mut r = SparseTT::Leaf { value: true };
        let mut idx = 0;
        for and in &cnf.ands {
            idx += 1;
            let clause: Vec<_> = and
                .iter()
                .map(|(ref vname, ref not)| (ctx.var(vname), *not))
                .collect();
            //r = r.and(SparseTT::from_clause(clause));
            r = r.and_clause(clause);
            r = r.simplify();
            println!("{}/{} tree size={}", idx, cnf.ands.len(), r.len());
        }
        r
    }

    pub fn from_clause(clause: Vec<(SparseTTVar, bool)>) -> SparseTT {
        let mut last = SparseTT::Leaf { value: false };
        for (SparseTTVar { id: ref var_id }, ref not) in clause.iter().rev() {
            let true_leaf = SparseTT::Leaf { value: true };
            let true_path;
            let false_path;
            if !*not {
                true_path = true_leaf;
                false_path = last;
            } else {
                true_path = last;
                false_path = true_leaf;
            }
            let x = SparseTT::Branch {
                variable: *var_id,
                false_path: Box::new(false_path),
                true_path: Box::new(true_path),
            };
            last = x;
        }
        last
    }

    pub fn and_clause(self, mut clause: Vec<(SparseTTVar, bool)>) -> SparseTT {
        match self {
            SparseTT::Branch {
                variable,
                mut false_path,
                mut true_path,
            } => {
                let target_path_op =
                    clause.iter().find_map(
                        |(ref var, ref not)| if var.id == variable { Some(*not) } else { None },
                    );
                if let Some(target_path) = target_path_op {
                    clause.retain(|(ref var, _)| var.id != variable);
                    if target_path == false {
                        *false_path = false_path.and_clause(clause);
                    } else {
                        *true_path = true_path.and_clause(clause);
                    }
                } else {
                    let clause2 = clause.clone();
                    *false_path = false_path.and_clause(clause);
                    *true_path = true_path.and_clause(clause2);
                }
                SparseTT::Branch {
                    variable,
                    false_path,
                    true_path,
                }
            }
            SparseTT::Leaf { value } => {
                if value {
                    return SparseTT::from_clause(clause);
                }
                SparseTT::Leaf { value }
            }
        }
    }

    pub fn not(self) -> SparseTT {
        match self {
            SparseTT::Branch {
                variable,
                mut false_path,
                mut true_path,
            } => {
                *false_path = false_path.not();
                *true_path = true_path.not();
                SparseTT::Branch {
                    variable,
                    false_path,
                    true_path,
                }
            }
            SparseTT::Leaf { value } => SparseTT::Leaf { value: !value },
        }
    }

    pub fn or(self, rhs: SparseTT) -> SparseTT {
        self.not().and(rhs.not()).not()
    }

    pub fn xor(self, rhs: SparseTT) -> SparseTT {
        let self2 = self.clone();
        let rhs2 = rhs.clone();
        self.not().and(rhs).or(self2.and(rhs2.not()))
    }

    pub fn eq(self, rhs: SparseTT) -> SparseTT {
        let self2 = self.clone();
        let rhs2 = rhs.clone();
        self.not().and(rhs.not()).or(self2.and(rhs2))
    }

    pub fn imp(self, rhs: SparseTT) -> SparseTT {
        self.not().or(rhs)
    }

    pub fn and(self, rhs: SparseTT) -> SparseTT {
        match self {
            SparseTT::Branch {
                variable,
                mut false_path,
                mut true_path,
            } => {
                let rhs_false = rhs.clone().reduce_node(&SparseTTLiteral {
                    var: SparseTTVar { id: variable },
                    not: true,
                });
                let rhs_true = rhs.reduce_node(&SparseTTLiteral {
                    var: SparseTTVar { id: variable },
                    not: false,
                });
                *false_path = false_path.and(rhs_false);
                *true_path = true_path.and(rhs_true);
                SparseTT::Branch {
                    variable,
                    false_path,
                    true_path,
                }
            }
            SparseTT::Leaf { value } => {
                if value {
                    rhs
                } else {
                    SparseTT::Leaf { value }
                }
            }
        }
    }

    pub fn and_mut(&mut self, rhs: &SparseTT) {
        *self = self.clone().and(rhs.clone());
    }

    pub fn reduce_node(self, lit: &SparseTTLiteral) -> Self {
        match self {
            SparseTT::Branch {
                variable,
                false_path,
                true_path,
            } => {
                if variable == lit.var.id {
                    if lit.not {
                        return *false_path;
                    } else {
                        return *true_path;
                    }
                }
                let false_path = Box::new(false_path.reduce_node(lit));
                let true_path = Box::new(true_path.reduce_node(lit));
                SparseTT::Branch {
                    variable,
                    false_path,
                    true_path,
                }
            }
            x => x,
        }
    }

    pub fn one_paths(&self) -> Vec<Vec<SparseTTLiteral>> {
        let mut result: Vec<Vec<SparseTTLiteral>> = Vec::new();
        let mut stack: Vec<(Vec<SparseTTLiteral>, &SparseTT)> = Vec::new();
        stack.push((Vec::new(), self));
        loop {
            if let Some((mut path, remainder)) = stack.pop() {
                match remainder {
                    &SparseTT::Branch {
                        ref variable,
                        ref false_path,
                        ref true_path,
                    } => {
                        let mut path2 = path.clone();
                        path.push(SparseTTLiteral {
                            var: SparseTTVar { id: *variable },
                            not: true,
                        });
                        path2.push(SparseTTLiteral {
                            var: SparseTTVar { id: *variable },
                            not: false,
                        });
                        stack.push((path, false_path));
                        stack.push((path2, true_path));
                    }
                    &SparseTT::Leaf { ref value } => {
                        if *value {
                            result.push(path);
                        }
                    }
                }
            } else {
                break;
            }
        }
        result
    }

    pub fn len(&self) -> usize {
        match self {
            &SparseTT::Branch {
                ref variable,
                ref false_path,
                ref true_path,
            } => false_path.len() + true_path.len(),
            &SparseTT::Leaf { ref value } => 1,
        }
    }

    pub fn simplify(self) -> Self {
        match self {
            SparseTT::Branch {
                variable,
                mut false_path,
                mut true_path,
            } => {
                *false_path = false_path.simplify();
                *true_path = true_path.simplify();
                if false_path.eq(&true_path) {
                    return *false_path;
                }
                SparseTT::Branch {
                    variable,
                    false_path,
                    true_path,
                }
            }
            x => x,
        }
    }
}

impl BitAnd for SparseTT {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        let mut result = self.clone();
        result.and_mut(&rhs);
        result
    }
}

impl BitAndAssign for SparseTT {
    fn bitand_assign(&mut self, rhs: Self) {
        self.and_mut(&rhs);
    }
}

impl fmt::Display for SparseTT {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum NodeOrString {
            Node(*const SparseTT),
            String(&'static str),
        };
        let mut queue: Vec<NodeOrString> = Vec::new();
        queue.push(NodeOrString::Node(self));
        loop {
            if queue.is_empty() {
                break;
            }
            let next = queue.remove(0);
            match next {
                NodeOrString::Node(node) => {
                    let node: &SparseTT = unsafe { &*node };
                    match node {
                        &SparseTT::Branch {
                            ref variable,
                            ref false_path,
                            ref true_path,
                        } => {
                            write!(formatter, "(x{}", variable)?;
                            queue.insert(0, NodeOrString::String(", "));
                            queue.insert(1, NodeOrString::Node(&**false_path));
                            queue.insert(2, NodeOrString::String(", "));
                            queue.insert(3, NodeOrString::Node(&**true_path));
                            queue.insert(4, NodeOrString::String(")"));
                        }
                        &SparseTT::Leaf { ref value } => {
                            write!(formatter, "{}", value)?;
                        }
                    }
                }
                NodeOrString::String(string) => {
                    write!(formatter, "{}", string)?;
                }
            }
        }
        Ok(())
    }
}

#[test]
fn test1() {
    // X AND Y = false
    // X OR Y = true
    let ad2 = AD2::solve_many(vec![AD2::x().and(AD2::y()).not(), AD2::x().or(AD2::y())]);
    let mut x: f64 = 0.3;
    let mut y: f64 = 0.8;
    let rate: f64 = 0.2;
    for it in 1..(100 + 1) {
        let z = ad2.eval(x, y);
        println!("it = {}", it);
        println!("x = {}", x);
        println!("y = {}", y);
        println!("z = {}", z);
        println!("______");
        let dz_dx = ad2.eval_df_dx(x, y);
        let dz_dy = ad2.eval_df_dy(x, y);
        let mut u = 1.0 / dz_dx;
        let mut v = 1.0 / dz_dy;
        let mut w = 1.0;
        let m = (u * u + v * v + w * w).sqrt();
        u /= m;
        v /= m;
        w /= m;
        x += -u * rate;
        y += -v * rate;
        if z <= 0.001 {
            break;
        }
    }
}

#[test]
fn test2() {
    let x1 = Expr::var(String::from("x1"));
    let expr = x1.clone().mult(x1);
    println!("expr = {}", expr);
    println!("dexpr_dx1 = {}", expr.dexp_dvar(&String::from("x1")));
}

#[test]
fn test3() {
    let a0 = BoolExpr::var('a', 0);
    let a1 = BoolExpr::var('a', 1);
    let a2 = BoolExpr::var('a', 2);
    let a3 = BoolExpr::var('a', 3);
    let b0 = BoolExpr::var('b', 0);
    let b1 = BoolExpr::var('b', 1);
    let b2 = BoolExpr::var('b', 2);
    let b3 = BoolExpr::var('b', 3);
    let r = BoolExpr::adder(vec![a3, a2, a1, a0], vec![b3, b2, b1, b0]);
    for i in 0..r.len() {
        println!("c[{}] = {}", i, r[i])
    }
}

#[test]
fn test4() {
    let cnf1 = CNF::var("a0")
        .or(CNF::var("a1"))
        .and(CNF::var("b0").or(CNF::var("b1")));
    let cnf2 = CNF::var("c0")
        .or(CNF::var("c1"))
        .and(CNF::var("d0").or(CNF::var("d1")));
    let cnf3 = CNF::var("a0")
        .or(CNF::var("a1"))
        .and(CNF::var("b0").or(CNF::var("b1")))
        .and(CNF::var("c0").or(CNF::var("c1")));
    println!("cnf1 = {}", cnf1);
    println!("cnf2 = {}", cnf2);
    println!("cnf3 = {}", cnf3);
    println!("cnf1 or cnf2 = {}", cnf1.clone().or(cnf2));
    println!("not cnf1 = {}", cnf1.not());
    println!("not cnf3 = {}", cnf3.not());
}

#[test]
fn test5() {
    let a0 = CNF::var("a0");
    let a1 = CNF::var("a1");
    let a2 = CNF::var("a2");
    let b0 = CNF::var("b0");
    let b1 = CNF::var("b1");
    let b2 = CNF::var("b2");
    let r = CNF::adder(vec![a2, a1, a0], vec![b2, b1, b0]);
    for i in 0..r.len() {
        println!("c[{}] = {}", i, r[i])
    }
}

#[test]
fn test6() {
    let a0 = BoolExpr::var('a', 0);
    let a1 = BoolExpr::var('a', 1);
    //let a2 = BoolExpr::var('a', 2);
    //let a3 = BoolExpr::var('a', 3);
    let b0 = BoolExpr::var('b', 0);
    let b1 = BoolExpr::var('b', 1);
    //let b2 = BoolExpr::var('b', 2);
    //let b3 = BoolExpr::var('b', 3);
    let r = BoolExpr::multiplier(vec![/*a3, a2,*/ a1, a0], vec![/*b3, b2,*/ b1, b0]);
    for i in 0..r.len() {
        println!("c[{}] = {}", i, r[i])
    }
}

#[test]
fn test7() {
    let mut circuit = Circuit::new();
    let a0 = circuit.alloc_var();
    let a1 = circuit.alloc_var();
    let a2 = circuit.alloc_var();
    let a3 = circuit.alloc_var();
    let b0 = circuit.alloc_var();
    let b1 = circuit.alloc_var();
    let b2 = circuit.alloc_var();
    let b3 = circuit.alloc_var();
    circuit.rename_var(a0, "a0");
    circuit.rename_var(a1, "a1");
    circuit.rename_var(a2, "a2");
    circuit.rename_var(a3, "a3");
    circuit.rename_var(b0, "b0");
    circuit.rename_var(b1, "b1");
    circuit.rename_var(b2, "b2");
    circuit.rename_var(b3, "b3");
    let r = circuit.multiplier(vec![a3, a2, a1, a0], vec![b3, b2, b1, b0]);
    for i in 0..r.len() {
        circuit.rename_var(r[i], format!("c{}", r.len() - 1 - i));
    }
    println!("{}", circuit);
    {
        let mut var_map: HashMap<String, bool> = HashMap::new();
        let evaluator = CircuitEvaluator::new(&circuit);
        var_map.insert("a0".into(), false);
        var_map.insert("a1".into(), false);
        var_map.insert("a2".into(), true);
        var_map.insert("a3".into(), false);
        var_map.insert("b0".into(), true);
        var_map.insert("b1".into(), true);
        var_map.insert("b2".into(), false);
        var_map.insert("b3".into(), false);
        evaluator.run(&mut var_map);
        for i in 0..r.len() {
            let c = format!("c{}", i);
            println!("{} = {}", c, var_map.get(&c).unwrap());
        }
    }
}

#[test]
fn test8() {
    let mut circuit = Circuit::new();
    let mut a = Vec::new();
    let mut b = Vec::new();
    for i in 0..4 {
        let x = circuit.alloc_var();
        a.push(x);
        circuit.rename_var(x, format!("a{}", i));
    }
    a.reverse();
    for i in 0..4 {
        let x = circuit.alloc_var();
        b.push(x);
        circuit.rename_var(x, format!("b{}", i));
    }
    b.reverse();
    let r = circuit.multiplier(a, b);
    for i in 0..r.len() {
        circuit.rename_var(r[i], format!("r{}", r.len() - 1 - i));
    }
    // lets factorize 1100
    // convert circuit into CNF, then solve with Expr
    let mut cnf = circuit.to_cnf();
    cnf.add_not_var_clause("r0");
    cnf.add_not_var_clause("r1");
    cnf.add_var_clause("r2");
    cnf.add_var_clause("r3");
    for i in 4..r.len() {
        cnf.add_not_var_clause(format!("r{}", i));
    }
    let expr = cnf.to_expr();
    let vars = expr.extract_vars();
    let mut var_map: HashMap<String, f64> = HashMap::new();
    let mut dexpr_dvar_map: HashMap<String, Expr> = HashMap::new();
    let mut rnd = Rng::new();
    for var in &vars {
        var_map.insert(var.clone(), rnd.rand() * 2.0 - 1.0);
        dexpr_dvar_map.insert(var.clone(), expr.dexp_dvar(var));
    }
    println!("{}", circuit);
    println!("----");
    println!("{}", cnf);
    println!("----");
    let sat = cnf.resolution();
    println!("{} {}", sat, cnf);
    println!("----");
    println!("{:?}", vars);
    println!("----");
    println!("{}", expr);
    println!("----");
    let rate: f64 = 0.2;
    let mut dz_dvar_map: HashMap<String, f64> = HashMap::new();
    for it in 1..(1000 + 1) {
        let z = expr.eval(&mut var_map).unwrap();
        println!("it = {}", it);
        for i in 0..4 {
            let var = format!("a{}", i);
            println!("{} = {}", var, var_map.get(&var).unwrap());
        }
        for i in 0..4 {
            let var = format!("b{}", i);
            println!("{} = {}", var, var_map.get(&var).unwrap());
        }
        println!("z = {}", z);
        println!("______");
        let mut m: f64 = 0.0;
        for var in &vars {
            let dz_dvar = dexpr_dvar_map.get(var).unwrap().eval(&mut var_map).unwrap();
            m += dz_dvar * dz_dvar;
            let found;
            if let Some(x) = dz_dvar_map.get_mut(var) {
                found = true;
                *x = dz_dvar;
            } else {
                found = false;
            }
            if !found {
                dz_dvar_map.insert(var.clone(), dz_dvar);
            }
        }
        m += 1.0;
        m = m.sqrt();
        for var in &vars {
            let dz_dvar = dz_dvar_map.get(var).unwrap();
            let mut x = *var_map.get(var).unwrap();
            x += -dz_dvar * rate / m;
            *var_map.get_mut(var).unwrap() = x;
        }
        if z <= 0.001 {
            break;
        }
    }
}

#[test]
fn test9() {
    let mut circuit = Circuit::new();
    let a = circuit.alloc_var();
    let b = circuit.alloc_var();
    let c = circuit.xor(a, b);
    circuit.rename_var(a, "a");
    circuit.rename_var(b, "b");
    circuit.rename_var(c, "c");
    let circuit_eval = CircuitEvaluator::new(&circuit);
    let mut dvar_map: HashMap<usize, (f64, Vec<f64>)> = HashMap::new();
    let mut rnd = Rng::new();
    dvar_map.insert(a.id, (rnd.rand(), vec![1.0, 0.0]));
    dvar_map.insert(b.id, (rnd.rand(), vec![0.0, 1.0]));
    println!("----");
    println!("{}", circuit);
    println!("----");
    let rate: f64 = 0.2;
    for it in 1..(100 + 1) {
        circuit_eval.run_numeric(&mut dvar_map);
        println!("----");
        println!("{:?}", dvar_map);
        println!("----");
        let out = dvar_map.get(&c.id).unwrap().0;
        let target = 1.0;
        let z = {
            let tmp = target - out;
            tmp * tmp
        };
        println!("it = {}", it);
        println!("{} = {}", "a", dvar_map.get(&a.id).unwrap().0);
        println!("{} = {}", "b", dvar_map.get(&b.id).unwrap().0);
        println!("z = {}", z);
        println!("______");
        let mut m: f64 = 0.0;
        {
            let dz_da = 2.0 * (out - target) * dvar_map.get(&c.id).unwrap().1[0];
            m += dz_da * dz_da;
        }
        {
            let dz_db = 2.0 * (out - target) * dvar_map.get(&c.id).unwrap().1[1];
            m += dz_db * dz_db;
        }
        m += 1.0;
        m = m.sqrt();
        {
            let dz_da = 2.0 * (out - target) * dvar_map.get(&c.id).unwrap().1[0];
            let dz_db = 2.0 * (out - target) * dvar_map.get(&c.id).unwrap().1[1];
            let a = dvar_map.get_mut(&a.id).unwrap();
            a.0 += -dz_da / m * rate;
            let b = dvar_map.get_mut(&b.id).unwrap();
            b.0 += -dz_db / m * rate;
        }
        if z <= 0.001 {
            break;
        }
    }
}

#[test]
fn test_factorize() {
    let mut circuit = Circuit::new();
    let mut a = Vec::new();
    let mut b = Vec::new();
    for i in 0..4 {
        let x = circuit.alloc_var();
        a.push(x);
        circuit.rename_var(x, format!("a{}", a.len() - 1 - i));
    }
    for i in 0..4 {
        let x = circuit.alloc_var();
        b.push(x);
        circuit.rename_var(x, format!("b{}", b.len() - 1 - i));
    }
    let r = circuit.multiplier(a.clone(), b.clone());
    for i in 0..r.len() {
        circuit.rename_var(r[i], format!("r{}", r.len() - 1 - i));
    }
    let circuit_eval = CircuitEvaluator::new(&circuit);
    let mut dvar_map: HashMap<usize, (f64, Vec<f64>)> = HashMap::new();
    let mut rnd = Rng::new();
    let _: f64 = rnd.rand();
    for i in 0..a.len() {
        let mut d = Vec::with_capacity(a.len() + b.len());
        for j in 0..a.len() + b.len() {
            if j == i {
                d.push(1.0);
            } else {
                d.push(0.0);
            }
        }
        dvar_map.insert(a[i].id, (rnd.rand(), d));
    }
    for i in 0..b.len() {
        let mut d = Vec::with_capacity(a.len() + b.len());
        for j in 0..a.len() + b.len() {
            if j == a.len() + i {
                d.push(1.0);
            } else {
                d.push(0.0);
            }
        }
        dvar_map.insert(b[i].id, (rnd.rand(), d));
    }
    // lets factorize 1111 (15 base 10)
    let mut target_r: Vec<f64> = Vec::new();
    target_r.push(0.0);
    target_r.push(0.0);
    target_r.push(0.0);
    target_r.push(0.0);
    target_r.push(1.0);
    target_r.push(1.0);
    target_r.push(1.0);
    target_r.push(1.0);
    println!("----");
    println!("{}", circuit);
    println!("----");
    let rate: f64 = 0.001;
    for it in 1..(1000000 + 1) {
        circuit_eval.run_numeric(&mut dvar_map);
        //println!("----");
        //println!("{:?}", dvar_map);
        //println!("----");
        let z = (0..r.len())
            .map(|i| {
                let tmp = dvar_map.get(&r[i].id).unwrap().0 - target_r[i];
                tmp * tmp
            })
            .fold(0.0, |a, b| a + b);
        println!("it = {}", it);
        for i in 0..4 {
            let var = format!("a{}", a.len() - 1 - i);
            println!("{} = {}", var, dvar_map.get(&a[i].id).unwrap().0);
        }
        for i in 0..4 {
            let var = format!("b{}", b.len() - 1 - i);
            println!("{} = {}", var, dvar_map.get(&b[i].id).unwrap().0);
        }
        println!("z = {}", z);
        println!("______");
        let mut m: f64 = 0.0;
        for i in 0..r.len() {
            let out = dvar_map.get(&r[i].id).unwrap().0;
            let target_out = target_r[i];
            for j in 0..a.len() {
                let dz_da = 2.0 * (out - target_out) * dvar_map.get(&r[i].id).unwrap().1[j];
                m += dz_da * dz_da;
            }
            for j in 0..b.len() {
                let dz_db =
                    2.0 * (out - target_out) * dvar_map.get(&r[i].id).unwrap().1[a.len() + j];
                m += dz_db * dz_db;
            }
        }
        m += 1.0;
        m = m.sqrt();
        for i in 0..r.len() {
            let out = dvar_map.get(&r[i].id).unwrap().0;
            let target_out = target_r[i];
            for j in 0..a.len() {
                let dz_da = 2.0 * (out - target_out) * dvar_map.get(&r[i].id).unwrap().1[j];
                let a = dvar_map.get_mut(&a[j].id).unwrap();
                let x = -dz_da * rate / m;
                a.0 += if x.is_nan() || x.is_infinite() {
                    0.0
                } else {
                    x
                }; // * rate / m;
            }
            for j in 0..b.len() {
                let dz_db =
                    2.0 * (out - target_out) * dvar_map.get(&r[i].id).unwrap().1[a.len() + j];
                let b = dvar_map.get_mut(&b[j].id).unwrap();
                let x = -dz_db * rate / m;
                b.0 += if x.is_nan() || x.is_infinite() {
                    0.0
                } else {
                    x
                }; // * rate / m;
            }
        }
        if z <= 0.001 {
            break;
        }
    }
}

#[test]
fn test_sparse_tt() {
    let mut sparse_tt_ctx = SparseTTContext::new();
    let x0 = sparse_tt_ctx.alloc_var("x0");
    let x1 = sparse_tt_ctx.alloc_var("x1");
    let x2 = sparse_tt_ctx.alloc_var("x2");
    let x3 = sparse_tt_ctx.alloc_var("x3");
    let sparse_tt = SparseTT::from_clause(vec![(x0, true), (x1, true), (x2, true)]);
    let sparse_tt2 = SparseTT::from_clause(vec![(x2, true), (x3, true)]);
    println!("{}", sparse_tt);
    println!();
    println!("{:?}", sparse_tt.one_paths());
    println!();
    println!(
        "{}",
        sparse_tt.clone().reduce_node(&SparseTTLiteral {
            var: SparseTTVar { id: 1 },
            not: true
        })
    );
    println!();
    println!("{}", sparse_tt & sparse_tt2);
}

#[test]
fn test10() {
    let mut circuit = Circuit::new();
    let mut a = Vec::new();
    let mut b = Vec::new();
    for i in 0..4 {
        let x = circuit.alloc_var();
        a.push(x);
        circuit.rename_var(x, format!("a{}", i));
    }
    a.reverse();
    for i in 0..4 {
        let x = circuit.alloc_var();
        b.push(x);
        circuit.rename_var(x, format!("b{}", i));
    }
    b.reverse();
    let r = circuit.multiplier(a, b);
    for i in 0..r.len() {
        circuit.rename_var(r[i], format!("r{}", r.len() - 1 - i));
    }
    // lets factorize 1111
    // convert circuit into CNF, then solve with Expr
    let mut cnf = circuit.to_cnf();
    cnf.add_var_clause("r0");
    cnf.add_var_clause("r1");
    cnf.add_var_clause("r2");
    cnf.add_var_clause("r3");
    for i in 4..r.len() {
        cnf.add_not_var_clause(format!("r{}", i));
    }
    let mut sparse_tt_ctx = SparseTTContext::new();
    let sparse_tt = SparseTT::from_cnf(&mut sparse_tt_ctx, &cnf);
    println!();
    println!("{} variables", sparse_tt_ctx.variable_name_map.len());
    println!();
    let one_paths = sparse_tt.one_paths();
    for one_path in one_paths {
        println!("----");
        for SparseTTLiteral {
            var: SparseTTVar { id },
            not,
        } in one_path
        {
            let vname = sparse_tt_ctx.variable_name_map.get(&id).unwrap();
            if vname.starts_with("var") {
                continue;
            }
            println!(
                "{} = {}",
                sparse_tt_ctx.variable_name_map.get(&id).unwrap(),
                !not
            );
        }
    }
}

#[test]
fn test11() {
    let _rsa_2048_str = "
        2519590847565789349402718324004839857142928212620403202777713783604366202070
        7595556264018525880784406918290641249515082189298559149176184502808489120072
        8449926873928072877767359714183472702618963750149718246911650776133798590957
        0009733045974880842840179742910064245869181719511874612151517265463228221686
        9987549182422433637259085141865462043576798423387184774447920739934236584823
        8242811981638150106748104516603773060562016196762561338441436038339044149526
        3443219011465754445417842402092461651572335077870774981712577246796292638635
        6373289912154831438167899885040445364023527381951378636564391212010397122822
        120720357";
    let _rsa_270_str = "
        2331085303444075445276376569106805241456198124803054490429486119684959182451
        3578286788836931857711641821391926857265831491306067262691135402760979316634
        1626693946596196427744273886601876896313468704059066746903123910748277606548
        649151920812699309766587514735456594993207";
    let _rsa_100_str = "1522605027922533360535618378132637429718068114961380688657908494580122963258952897654000350692006139";
    let small_str = "39";
    let mut input_str = small_str.to_string();
    input_str.retain(|c| !c.is_whitespace());
    let input = BigInt::from_str(input_str.as_str()).unwrap();
    let mut target_r: Vec<f64> = Vec::new();
    {
        let mut input = input.clone();
        let zero = BigInt::from(0i32);
        let one = BigInt::from(1i32);
        while !input.eq(&zero) {
            let bit = input.clone() & one.clone();
            if bit.eq(&one) {
                target_r.push(1.0);
            } else {
                target_r.push(0.0);
            }
            input >>= 1;
        }
    }
    {
        let tmp = target_r.len() * 3;
        while target_r.len() < tmp {
            target_r.push(0.0);
        }
    }
    target_r.reverse();
    let mut circuit = Circuit::new();
    let mut a = Vec::new();
    let mut b = Vec::new();
    for i in 0..(target_r.len() / 2) {
        let x = circuit.alloc_var();
        a.push(x);
        circuit.rename_var(x, format!("a{}", i));
    }
    a.reverse();
    for i in 0..(target_r.len() / 2) {
        let x = circuit.alloc_var();
        b.push(x);
        circuit.rename_var(x, format!("b{}", i));
    }
    b.reverse();
    print!("Creating circuit... ");
    std::io::stdout().flush().unwrap_or(());
    let r = circuit.multiplier(a.clone(), b.clone());
    println!("done.");
    for i in 0..r.len() {
        circuit.rename_var(r[i], format!("r{}", r.len() - 1 - i));
    }
    let circuit_eval = CircuitEvaluator::new(&circuit);
    let mut dvar_map: HashMap<usize, (f64, Vec<f64>)> = HashMap::new();
    let mut rnd = Rng::new();
    let _: f64 = rnd.rand();
    for i in 0..a.len() {
        let mut d = Vec::with_capacity(a.len() + b.len());
        for j in 0..a.len() + b.len() {
            if j == i {
                d.push(1.0);
            } else {
                d.push(0.0);
            }
        }
        dvar_map.insert(a[i].id, (rnd.rand(), d));
    }
    for i in 0..b.len() {
        let mut d = Vec::with_capacity(a.len() + b.len());
        for j in 0..a.len() + b.len() {
            if j == a.len() + i {
                d.push(1.0);
            } else {
                d.push(0.0);
            }
        }
        dvar_map.insert(b[i].id, (rnd.rand(), d));
    }
    //println!("----");
    //println!("{}", circuit);
    //println!("----");
    drop(circuit);
    let rate: f64 = 0.001;
    println!("start of solver");
    for it in 1..(1000000 + 1) {
        circuit_eval.run_numeric(&mut dvar_map);
        //println!("----");
        //println!("{:?}", dvar_map);
        //println!("----");
        let z = (0..r.len())
            .map(|i| {
                let tmp = dvar_map.get(&r[i].id).unwrap().0 - target_r[i];
                tmp * tmp
            })
            .fold(0.0, |a, b| a + b);
        println!("it = {}", it);
        /*
        for i in 0..4 {
            let var = format!("a{}", a.len()-1-i);
            println!("{} = {}", var, dvar_map.get(&a[i].id).unwrap().0);
        }
        for i in 0..4 {
            let var = format!("b{}", b.len()-1-i);
            println!("{} = {}", var, dvar_map.get(&b[i].id).unwrap().0);
        }*/
        println!("error = {}", z);
        println!("______");
        let mut m: f64 = 0.0;
        for i in 0..r.len() {
            let out = dvar_map.get(&r[i].id).unwrap().0;
            let target_out = target_r[i];
            for j in 0..a.len() {
                let dz_da = 2.0 * (out - target_out) * dvar_map.get(&r[i].id).unwrap().1[j];
                m += dz_da * dz_da;
            }
            for j in 0..b.len() {
                let dz_db =
                    2.0 * (out - target_out) * dvar_map.get(&r[i].id).unwrap().1[a.len() + j];
                m += dz_db * dz_db;
            }
        }
        m += 1.0;
        m = m.sqrt();
        for i in 0..r.len() {
            let out = dvar_map.get(&r[i].id).unwrap().0;
            let target_out = target_r[i];
            for j in 0..a.len() {
                let dz_da = 2.0 * (out - target_out) * dvar_map.get(&r[i].id).unwrap().1[j];
                let a = dvar_map.get_mut(&a[j].id).unwrap();
                let x = -dz_da * rate / m;
                a.0 += if x.is_nan() || x.is_infinite() {
                    0.0
                } else {
                    x
                }; // * rate / m;
            }
            for j in 0..b.len() {
                let dz_db =
                    2.0 * (out - target_out) * dvar_map.get(&r[i].id).unwrap().1[a.len() + j];
                let b = dvar_map.get_mut(&b[j].id).unwrap();
                let x = -dz_db * rate / m;
                b.0 += if x.is_nan() || x.is_infinite() {
                    0.0
                } else {
                    x
                }; // * rate / m;
            }
        }
        if z <= 0.001 {
            break;
        }
    }
    println!();
    for x in &a {
        println!(
            "{} = {}",
            circuit_eval.id_to_name(&x.id),
            dvar_map.get(&x.id).unwrap().0
        );
    }
    println!();
    for x in &b {
        println!(
            "{} = {}",
            circuit_eval.id_to_name(&x.id),
            dvar_map.get(&x.id).unwrap().0
        );
    }
    println!();
    for x in &r {
        println!(
            "{} = {}",
            circuit_eval.id_to_name(&x.id),
            dvar_map.get(&x.id).unwrap().0
        );
    }
    println!();
}

#[test]
fn test12() {
    let _rsa_2048_str = "
        2519590847565789349402718324004839857142928212620403202777713783604366202070
        7595556264018525880784406918290641249515082189298559149176184502808489120072
        8449926873928072877767359714183472702618963750149718246911650776133798590957
        0009733045974880842840179742910064245869181719511874612151517265463228221686
        9987549182422433637259085141865462043576798423387184774447920739934236584823
        8242811981638150106748104516603773060562016196762561338441436038339044149526
        3443219011465754445417842402092461651572335077870774981712577246796292638635
        6373289912154831438167899885040445364023527381951378636564391212010397122822
        120720357";
    let _rsa_270_str = "
        2331085303444075445276376569106805241456198124803054490429486119684959182451
        3578286788836931857711641821391926857265831491306067262691135402760979316634
        1626693946596196427744273886601876896313468704059066746903123910748277606548
        649151920812699309766587514735456594993207";
    let _rsa_100_str = "1522605027922533360535618378132637429718068114961380688657908494580122963258952897654000350692006139";
    let small_str = "39";
    let mut input_str = small_str.to_string();
    input_str.retain(|c| !c.is_whitespace());
    let input = BigInt::from_str(input_str.as_str()).unwrap();
    let mut circuit = Circuit::new();
    let mut a = Vec::new();
    let mut b = Vec::new();
    for i in 0..4 {
        let x = circuit.alloc_var();
        a.push(x);
        circuit.rename_var(x, format!("a{}", i));
    }
    a.reverse();
    for i in 0..4 {
        let x = circuit.alloc_var();
        b.push(x);
        circuit.rename_var(x, format!("b{}", i));
    }
    b.reverse();
    print!("Creating circuit... ");
    std::io::stdout().flush().unwrap_or(());
    let mut r = circuit.multiplier(a.clone(), b.clone());
    a.reverse();
    b.reverse();
    r.reverse();
    println!("done.");
    for i in 0..r.len() {
        circuit.rename_var(r[i], format!("r{}", i));
    }
    let c1 = circuit.not_eq_to_one_lsb(&a);
    let c2 = circuit.not_eq_to_one_lsb(&b);
    let c3 = circuit.lte_lsb(&a, &b);
    let mut cnf = circuit.to_cnf();
    for constraint in [c1, c2, c3].iter() {
        let x = constraint.id as usize;
        cnf.assign_lit(circuit.var_names.get(&x).unwrap().clone(), true);
    }
    {
        let mut input = input.clone();
        let zero = BigInt::from(0i32);
        let one = BigInt::from(1i32);
        let mut idx = 0;
        while !input.eq(&zero) {
            let bit = input.clone() & one.clone();
            let r = format!("r{}", idx);
            if bit.eq(&one) {
                cnf.assign_lit(r, true);
            } else {
                cnf.assign_lit(r, false);
            }
            input >>= 1;
            idx += 1;
        }
        for i in idx..r.len() {
            let r = format!("r{}", i);
            cnf.assign_lit(r, false);
        }
    }
    let mut sparse_tt_ctx = SparseTTContext::new();
    let sparse_tt = SparseTT::from_cnf(&mut sparse_tt_ctx, &cnf);
    println!();
    println!("{} variables", sparse_tt_ctx.variable_name_map.len());
    println!();
    let one_paths = sparse_tt.one_paths();
    for one_path in one_paths {
        println!("----");
        let mut result: Vec<String> = Vec::new();
        for SparseTTLiteral {
            var: SparseTTVar { id },
            not,
        } in one_path
        {
            let vname = sparse_tt_ctx.variable_name_map.get(&id).unwrap();
            if vname.starts_with("var") {
                continue;
            }
            result.push(format!(
                "{} = {}",
                sparse_tt_ctx.variable_name_map.get(&id).unwrap(),
                !not
            ));
        }
        result.sort();
        for line in result {
            println!("{}", line);
        }
    }
}

#[test]
fn test13() {
    let small_str = "39";
    let mut input_str = small_str.to_string();
    input_str.retain(|c| !c.is_whitespace());
    let input = BigInt::from_str(input_str.as_str()).unwrap();
    let mut circuit = Circuit::new();
    let mut a = Vec::new();
    let mut b = Vec::new();
    for i in 0..4 {
        let x = circuit.alloc_var();
        a.push(x);
        circuit.rename_var(x, format!("a{}", i));
    }
    a.reverse();
    for i in 0..4 {
        let x = circuit.alloc_var();
        b.push(x);
        circuit.rename_var(x, format!("b{}", i));
    }
    b.reverse();
    print!("Creating circuit... ");
    std::io::stdout().flush().unwrap_or(());
    let mut r = circuit.multiplier(a.clone(), b.clone());
    a.reverse();
    b.reverse();
    r.reverse();
    println!("done.");
    for i in 0..r.len() {
        circuit.rename_var(r[i], format!("r{}", i));
    }
    let c1 = circuit.not_eq_to_one_lsb(&a);
    let c2 = circuit.not_eq_to_one_lsb(&b);
    let c3 = circuit.lte_lsb(&a, &b);
    let mut cnf = circuit.to_3sat();
    for constraint in [c1, c2, c3].iter() {
        let x = constraint.id as isize;
        cnf.assign_lit(x);
    }
    {
        let mut input = input.clone();
        let zero = BigInt::from(0i32);
        let one = BigInt::from(1i32);
        let mut idx = 0;
        while !input.eq(&zero) {
            let bit = input.clone() & one.clone();
            let var = r[idx].id as isize;
            if bit.eq(&one) {
                cnf.assign_lit(var);
            } else {
                cnf.assign_lit(-var);
            }
            input >>= 1;
            idx += 1;
        }
        for i in idx..r.len() {
            let var = r[i].id as isize;
            cnf.assign_lit(-var);
        }
    }
    // println!("{}", if cnf.is_sat() { "SAT" } else { "UNSAT" });
    let mut sat = Sat::from_clauses(cnf.clauses.iter().map(|x| vec![x[0], x[1], x[2]]).collect());
    println!("{}", sat);
    println!();
    let mut sat2 = sat.clone();
    sat2.simplify();
    println!("{}", sat2);
    let result_op = sat.solve();
    println!(
        "{:?}",
        result_op.map(|x| {
            let mut y: Vec<isize> = x.iter().map(|x| *x).collect();
            y.sort();
            y
        })
    );
}

#[test]
fn test14() {
    let small_str = "39";
    let mut input_str = small_str.to_string();
    input_str.retain(|c| !c.is_whitespace());
    let input = BigInt::from_str(input_str.as_str()).unwrap();
    let mut circuit = Circuit::new();
    let mut a = Vec::new();
    let mut b = Vec::new();
    for i in 0..4 {
        let x = circuit.alloc_var();
        a.push(x);
        circuit.rename_var(x, format!("a{}", i));
    }
    a.reverse();
    for i in 0..4 {
        let x = circuit.alloc_var();
        b.push(x);
        circuit.rename_var(x, format!("b{}", i));
    }
    b.reverse();
    print!("Creating circuit... ");
    std::io::stdout().flush().unwrap_or(());
    let mut r = circuit.multiplier(a.clone(), b.clone());
    a.reverse();
    b.reverse();
    r.reverse();
    println!("done.");
    for i in 0..r.len() {
        circuit.rename_var(r[i], format!("r{}", i));
    }
    let mut cnf = circuit.to_3sat();
    {
        let mut input = input.clone();
        let zero = BigInt::from(0i32);
        let one = BigInt::from(1i32);
        let mut idx = 0;
        while !input.eq(&zero) {
            let bit = input.clone() & one.clone();
            let var = r[idx].id as isize;
            if bit.eq(&one) {
                cnf.assign_lit(var);
            } else {
                cnf.assign_lit(-var);
            }
            input >>= 1;
            idx += 1;
        }
        for i in idx..r.len() {
            let var = r[idx].id as isize;
            cnf.assign_lit(-var);
        }
    }
    println!("{}", cnf);
    for it in 1..(10 + 1) {
        println!();
        let mut sat = _1InAllSat::from_3sat(&cnf);
        println!("{}", sat);
        let result_op = sat.solve();
        println!();
        println!(
            "{:?}",
            result_op.clone().map(|x| {
                let mut y: Vec<isize> = x.iter().map(|x| *x).collect();
                y.sort();
                y
            })
        );
        if let Some(result) = result_op {
            let mut max_var = 1;
            for clause in &cnf.clauses {
                for lit in clause {
                    let var = lit.abs();
                    if var > max_var {
                        max_var = var;
                    }
                }
            }
            let mut any_assigned = false;
            for lit in result {
                if lit.abs() <= max_var {
                    cnf.assign_lit(lit);
                    any_assigned = true;
                }
            }
            if !any_assigned {
                println!();
                println!("{}", cnf);
                return;
            }
        }
        println!();
        println!("{}", cnf);
    }
}

#[test]
fn test15() {
    let rsa_2048_str = "
        2519590847565789349402718324004839857142928212620403202777713783604366202070
        7595556264018525880784406918290641249515082189298559149176184502808489120072
        8449926873928072877767359714183472702618963750149718246911650776133798590957
        0009733045974880842840179742910064245869181719511874612151517265463228221686
        9987549182422433637259085141865462043576798423387184774447920739934236584823
        8242811981638150106748104516603773060562016196762561338441436038339044149526
        3443219011465754445417842402092461651572335077870774981712577246796292638635
        6373289912154831438167899885040445364023527381951378636564391212010397122822
        120720357";
    let _rsa_270_str = "
        2331085303444075445276376569106805241456198124803054490429486119684959182451
        3578286788836931857711641821391926857265831491306067262691135402760979316634
        1626693946596196427744273886601876896313468704059066746903123910748277606548
        649151920812699309766587514735456594993207";
    let _rsa_100_str = "1522605027922533360535618378132637429718068114961380688657908494580122963258952897654000350692006139";
    let small_str = "39";
    let mut input_str = small_str.to_string();
    input_str.retain(|c| !c.is_whitespace());
    let input = BigInt::from_str(input_str.as_str()).unwrap();
    let mut circuit = Circuit::new();
    let mut sparse_tt_ctx = SparseTTContext::new();
    let mut var_map = HashMap::new();
    let mut a = Vec::new();
    let mut b = Vec::new();
    for i in 0..4 {
        let x = circuit.alloc_var();
        a.push(x);
        let vname = format!("a{}", i);
        circuit.rename_var(x, vname.clone());
        let tmp = sparse_tt_ctx.alloc_var(vname.clone());
        var_map.insert(vname, SparseTT::from_clause(vec![(tmp, false)]));
    }
    a.reverse();
    for i in 0..4 {
        let x = circuit.alloc_var();
        b.push(x);
        let vname = format!("b{}", i);
        circuit.rename_var(x, vname.clone());
        let tmp = sparse_tt_ctx.alloc_var(vname.clone());
        var_map.insert(vname, SparseTT::from_clause(vec![(tmp, false)]));
    }
    b.reverse();
    print!("Creating circuit... ");
    std::io::stdout().flush().unwrap_or(());
    let r = circuit.multiplier(a.clone(), b.clone());
    a.reverse();
    b.reverse();
    println!("done.");
    for i in 0..r.len() {
        circuit.rename_var(r[i], format!("r{}", r.len() - 1 - i));
    }
    let c1 = circuit.not_eq_to_one_lsb(&a);
    let c2 = circuit.not_eq_to_one_lsb(&b);
    circuit.rename_var(c1, "c1");
    circuit.rename_var(c2, "c2");
    let circuit_eval = CircuitEvaluator::new(&circuit);
    circuit_eval.run_sparse_tt(&mut var_map);
    let mut sparse_tt = SparseTT::Leaf { value: true };
    for constraint in ["c1", "c2"].iter() {
        let c = var_map.get(&constraint.to_string()).unwrap();
        sparse_tt = sparse_tt.and(c.clone());
    }
    {
        let mut input = input.clone();
        let zero = BigInt::from(0i32);
        let one = BigInt::from(1i32);
        let mut idx = 0;
        while !input.eq(&zero) {
            let bit = input.clone() & one.clone();
            let r = format!("r{}", idx);
            if let Some(tmp) = var_map.get(&r) {
                let tmp = tmp.clone();
                if bit.eq(&one) {
                    sparse_tt = sparse_tt.and(tmp);
                } else {
                    sparse_tt = sparse_tt.and(tmp.not());
                }
            }
            input >>= 1;
            idx += 1;
        }
    }
    println!();
    println!("{} variables", sparse_tt_ctx.variable_name_map.len());
    println!();
    let one_paths = sparse_tt.one_paths();
    for one_path in one_paths {
        println!("----");
        let mut result: Vec<String> = Vec::new();
        for SparseTTLiteral {
            var: SparseTTVar { id },
            not,
        } in one_path
        {
            let vname = sparse_tt_ctx.variable_name_map.get(&id).unwrap();
            if vname.starts_with("var") {
                continue;
            }
            result.push(format!(
                "{} = {}",
                sparse_tt_ctx.variable_name_map.get(&id).unwrap(),
                !not
            ));
        }
        result.sort();
        for line in result {
            println!("{}", line);
        }
    }
}

fn main() {
    let small_str = "39";
    let mut input_str = small_str.to_string();
    input_str.retain(|c| !c.is_whitespace());
    let input = BigInt::from_str(input_str.as_str()).unwrap();
    let mut circuit = Circuit::new();
    let mut a = Vec::new();
    let mut b = Vec::new();
    for i in 0..4 {
        let x = circuit.alloc_var();
        a.push(x);
        circuit.rename_var(x, format!("a{}", i));
    }
    a.reverse();
    for i in 0..4 {
        let x = circuit.alloc_var();
        b.push(x);
        circuit.rename_var(x, format!("b{}", i));
    }
    b.reverse();
    print!("Creating circuit... ");
    std::io::stdout().flush().unwrap_or(());
    let mut r = circuit.multiplier(a.clone(), b.clone());
    a.reverse();
    b.reverse();
    r.reverse();
    println!("done.");
    for i in 0..r.len() {
        circuit.rename_var(r[i], format!("r{}", i));
    }
    let c1 = circuit.not_eq_to_one_lsb(&a);
    let c2 = circuit.not_eq_to_one_lsb(&b);
    let c3 = circuit.lte_lsb(&a, &b);
    let mut cnf = circuit.to_sat();
    for constraint in [c1, c2, c3].iter() {
        let x = constraint.id as isize;
        cnf.assign_lit(x);
    }
    {
        let mut input = input.clone();
        let zero = BigInt::from(0i32);
        let one = BigInt::from(1i32);
        let mut idx = 0;
        while !input.eq(&zero) {
            let bit = input.clone() & one.clone();
            let var = r[idx].id as isize;
            if bit.eq(&one) {
                cnf.assign_lit(var);
            } else {
                cnf.assign_lit(-var);
            }
            input >>= 1;
            idx += 1;
        }
        for i in idx..r.len() {
            let var = r[i].id as isize;
            cnf.assign_lit(-var);
        }
    }
    // println!("{}", if cnf.is_sat() { "SAT" } else { "UNSAT" });
    let mut sat = cnf;
    println!("{}", sat);
    println!();

    /*
    let cnf2 = CnfFormula::from(sat.clauses.clone());
    let mut solver_ctx = solver2::SolverCtx::new(&cnf2);
    solver_ctx.solve();
    println!();
    */

    let mut solver_ctx = solver1::SolverCtx::new();
    solver_ctx.add_clauses(sat);
    let result_op = solver_ctx.solve();
    println!(
        "{:?}",
        result_op /*
                  result_op.map(|x| {
                      let mut y: Vec<isize> = x.iter().map(|x| *x).collect();
                      y.sort();
                      y
                  })
                  */
    );
}
