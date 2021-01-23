use crate::Expr;
use std::cmp::max;
use std::collections::HashSet;
use std::fmt;

#[derive(Clone)]
pub struct CNF {
    pub ands: Vec<Vec<(String, bool)>>,
}

pub struct CNFAdderResult {
    pub carry: CNF,
    pub out: CNF,
}

impl CNF {
    pub fn assign_lit(&mut self, var: String, val: bool) {
        let not = !val;
        for i in (0..self.ands.len()).rev() {
            let found = self.ands[i]
                .iter()
                .any(|&(ref var2, ref not2)| var2.eq(&var) && *not2 == not);
            if found {
                self.ands.remove(i);
            } else {
                self.ands[i].retain(|&(ref var2, ref not2)| !(var2.eq(&var) && *not2 != not));
            }
        }
    }

    pub fn add_var_clause<VarName: Into<String>>(&mut self, var_name: VarName) {
        self.ands.push(vec![(var_name.into(), false)]);
    }

    pub fn add_not_var_clause<VarName: Into<String>>(&mut self, var_name: VarName) {
        self.ands.push(vec![(var_name.into(), true)]);
    }

    pub fn add_var_clause_first<VarName: Into<String>>(&mut self, var_name: VarName) {
        self.ands.insert(0, vec![(var_name.into(), false)]);
    }

    pub fn add_not_var_clause_first<VarName: Into<String>>(&mut self, var_name: VarName) {
        self.ands.insert(0, vec![(var_name.into(), true)]);
    }

    pub fn var<Name: Into<String>>(name: Name) -> CNF {
        CNF {
            ands: vec![vec![(name.into(), false)]],
        }
    }

    pub fn and(mut self, mut rhs: CNF) -> CNF {
        self.ands.append(&mut rhs.ands);
        self.simplify()
    }

    pub fn or(self, rhs: CNF) -> CNF {
        // {A,B},{C,D} or {E,F},{G,H}
        // {A,B,E,F},{A,B,G,H},{C,D,E,F},{C,D,G,H}
        let mut result_ands = Vec::new();
        for lhs_ors in &self.ands {
            for rhs_ors in &rhs.ands {
                let mut result_ors = lhs_ors.clone();
                for rhs_or in rhs_ors {
                    result_ors.push(rhs_or.clone());
                }
                result_ands.push(result_ors);
            }
        }
        let result = CNF { ands: result_ands };
        result.simplify()
    }

    pub fn not(self) -> CNF {
        // !({A,B},{C,D})
        // !((A or B) and (C or D))
        // !(A or B) or !(C or D)
        // (!A and !B) or (!C and !D)
        // (!A or !C) and (!A or !D) and (!B or !C) and (!B or !D)
        // {!A,!C},{!A,!D},{!B,!C},{!B,!D}
        // ({!A},{!B}) or ({!C},{!D})
        let mut tmp_cnfs = Vec::new();
        for lhs_ors in &self.ands {
            let mut tmp_cnf_ands = Vec::new();
            for (ref name, ref not) in lhs_ors {
                tmp_cnf_ands.push(vec![(name.clone(), !*not)]);
            }
            tmp_cnfs.push(CNF { ands: tmp_cnf_ands });
        }
        let mut cnf = tmp_cnfs[0].clone();
        for i in 1..tmp_cnfs.len() {
            cnf = cnf.or(tmp_cnfs[i].clone())
        }
        cnf.simplify()
    }

    pub fn xor(self, rhs: CNF) -> CNF {
        let self2 = self.clone();
        let rhs2 = rhs.clone();
        self.not().and(rhs).or(self2.and(rhs2.not()))
    }

    pub fn half_adder(bit1: CNF, bit2: CNF) -> CNFAdderResult {
        let bit12 = bit1.clone();
        let bit22 = bit2.clone();
        CNFAdderResult {
            out: bit1.xor(bit2),
            carry: bit12.and(bit22),
        }
    }

    pub fn full_adder(bit1: CNF, bit2: CNF, carry: CNF) -> CNFAdderResult {
        let r1 = CNF::half_adder(bit1, bit2);
        let r2 = CNF::half_adder(r1.out, carry);
        CNFAdderResult {
            out: r2.out,
            carry: r1.carry.or(r2.carry),
        }
    }

    pub fn adder(lhs_bits: Vec<CNF>, rhs_bits: Vec<CNF>) -> Vec<CNF> {
        let n = max(lhs_bits.len(), rhs_bits.len());
        if n == 0 {
            return Vec::new();
        }
        let mut result = Vec::new();
        let mut carry;
        {
            let lhs = lhs_bits[0].clone();
            let rhs = rhs_bits[0].clone();
            let CNFAdderResult { out, carry: carry2 } = CNF::half_adder(lhs, rhs);
            carry = carry2;
            result.push(out);
        }
        for i in 1..n {
            let lhs = lhs_bits[i].clone();
            let rhs = rhs_bits[i].clone();
            let CNFAdderResult { out, carry: carry2 } = CNF::full_adder(lhs, rhs, carry.clone());
            carry = carry2;
            result.push(out);
        }
        for i in n..lhs_bits.len() {
            let lhs = lhs_bits[i].clone();
            let CNFAdderResult { out, carry: carry2 } = CNF::half_adder(lhs, carry.clone());
            carry = carry2;
            result.push(out);
        }
        for i in n..rhs_bits.len() {
            let rhs = rhs_bits[i].clone();
            let CNFAdderResult { out, carry: carry2 } = CNF::half_adder(rhs, carry.clone());
            carry = carry2;
            result.push(out);
        }
        result.push(carry);
        result.reverse();
        result
    }

    pub fn resolution(&mut self) -> bool {
        let comparator = |(ref a_name, ref a_not): &(String, bool),
                          (ref b_name, ref b_not): &(String, bool)| {
            if a_name == b_name {
                a_not.cmp(b_not)
            } else {
                a_name.cmp(b_name)
            }
        };
        let mut var_set: HashSet<String> = HashSet::new();
        let mut visited_pairs: HashSet<(usize, usize)> = HashSet::new();
        for ors in &self.ands {
            for (ref var, ref _not) in ors {
                var_set.insert(var.clone());
            }
        }
        for var in var_set {
            println!();
            println!("joining {}", var);
            loop {
                let i_op = self
                    .ands
                    .iter()
                    .position(|ors| ors.iter().any(|(ref var2, ref not)| var2.eq(&var) && !not));
                let j_op = self
                    .ands
                    .iter()
                    .position(|ors| ors.iter().any(|(ref var2, ref not)| var2.eq(&var) && *not));
                let mut again = false;
                if let Some(i) = i_op {
                    if let Some(j) = j_op {
                        let i2;
                        let j2;
                        if j < i {
                            i2 = j;
                            j2 = i;
                        } else {
                            i2 = i;
                            j2 = j;
                        }
                        println!("({},{})", i2, j2);
                        if j2 == i2 {
                            self.ands.remove(i2);
                            continue;
                        }
                        self.ands[j2].retain(|(ref var2, ref not)| !(var2.eq(&var) && !not));
                        let mut tmp = self.ands.remove(j2);
                        let i_ors = &mut self.ands[i2];
                        i_ors.retain(|(var2, not)| !(var2.eq(&var) && *not));
                        i_ors.append(&mut tmp);
                        i_ors.sort_by(comparator);
                        i_ors.dedup();
                        let empty = i_ors.is_empty();
                        if empty {
                            return false;
                        }
                        again = true;
                    }
                }
                if !again {
                    break;
                }
            }
        }
        return true;
    }

    pub fn simplify(mut self) -> CNF {
        let comparator = |(ref a_name, ref a_not): &(String, bool),
                          (ref b_name, ref b_not): &(String, bool)| {
            if a_name == b_name {
                a_not.cmp(b_not)
            } else {
                a_name.cmp(b_name)
            }
        };
        for ors in &mut self.ands {
            ors.sort_by(comparator);
            ors.dedup();
            let ors2 = ors.clone();
            ors.retain(|(ref a_name, ref a_not)| {
                !ors2.iter().any(|(ref b_name, ref b_not)| {
                    a_name.cmp(b_name) == std::cmp::Ordering::Equal && *a_not == !*b_not
                })
            });
        }
        self
    }

    pub fn to_expr(&self) -> Expr {
        let and_exprs: Vec<Expr> = self
            .ands
            .iter()
            .filter_map(|ors| Self::ors_to_expr(ors))
            .collect();
        if and_exprs.is_empty() {
            panic!("{}", "Invalid CNF.");
        }
        let mut expr = and_exprs[0].clone();
        for i in 1..and_exprs.len() {
            let tmp = and_exprs[i].clone();
            expr = expr.add(tmp.squared());
        }
        expr
    }

    fn ors_to_expr(ors: &Vec<(String, bool)>) -> Option<Expr> {
        if ors.is_empty() {
            return None;
        }
        let mut expr = Self::var_to_expr(&ors[0]);
        for i in 1..ors.len() {
            expr = expr.mult(Self::var_to_expr(&ors[i]));
        }
        Some(expr)
    }

    fn var_to_expr(var: &(String, bool)) -> Expr {
        let (ref vname, ref not) = var;
        let vexpr = Expr::var(vname.clone());
        let offset = if *not { 1.0 } else { -1.0 };
        Expr::add(vexpr, Expr::const_(offset))
    }
}

impl fmt::Display for CNF {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first_and = true;
        for ors in &self.ands {
            if first_and {
                first_and = false;
            } else {
                write!(formatter, ",")?;
            }
            let mut first_or = true;
            write!(formatter, "{{")?;
            for (ref name, ref not) in ors {
                if first_or {
                    first_or = false;
                } else {
                    write!(formatter, ",")?;
                }
                if *not {
                    write!(formatter, "!")?;
                }
                write!(formatter, "{}", name)?;
            }
            write!(formatter, "}}")?;
        }
        Ok(())
    }
}
