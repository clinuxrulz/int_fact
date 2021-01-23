use crate::{Anf, Sat, _3Sat, CNF};
use std::cmp::min;
use std::collections::HashMap;
use std::fmt;

pub struct Circuit {
    pub gates: Vec<CircuitGate>,
    pub next_var_id: usize,
    pub var_names: HashMap<usize, String>,
}

pub struct CircuitAdderResult {
    pub out: CircuitVar,
    pub carry: CircuitVar,
}

impl Circuit {
    pub fn new() -> Circuit {
        Circuit {
            gates: Vec::new(),
            next_var_id: 1,
            var_names: HashMap::new(),
        }
    }

    pub fn alloc_var(&mut self) -> CircuitVar {
        let result = CircuitVar {
            id: self.next_var_id,
        };
        self.var_names
            .insert(result.id, format!("var_{}", result.id));
        self.next_var_id += 1;
        result.into()
    }

    pub fn rename_var<NewVarName: Into<String>>(
        &mut self,
        var: CircuitVar,
        new_var_name: NewVarName,
    ) {
        if let Some(var_name) = self.var_names.get_mut(&var.id) {
            *var_name = new_var_name.into();
        }
    }

    pub fn and(&mut self, in1: CircuitVar, in2: CircuitVar) -> CircuitVar {
        let out = self.alloc_var();
        self.gates.push(CircuitGate::And(in1, in2, out));
        out
    }

    pub fn or(&mut self, in1: CircuitVar, in2: CircuitVar) -> CircuitVar {
        let out = self.alloc_var();
        self.gates.push(CircuitGate::Or(in1, in2, out));
        out
    }

    pub fn not(&mut self, in_: CircuitVar) -> CircuitVar {
        let out = self.alloc_var();
        self.gates.push(CircuitGate::Not(in_, out));
        out
    }

    pub fn xor(&mut self, in1: CircuitVar, in2: CircuitVar) -> CircuitVar {
        let out = self.alloc_var();
        self.gates.push(CircuitGate::Xor(in1, in2, out));
        out
    }

    pub fn imp(&mut self, in1: CircuitVar, in2: CircuitVar) -> CircuitVar {
        let out = self.alloc_var();
        self.gates.push(CircuitGate::Imp(in1, in2, out));
        out
    }

    pub fn eq(&mut self, in1: CircuitVar, in2: CircuitVar) -> CircuitVar {
        let out = self.alloc_var();
        self.gates.push(CircuitGate::Eq(in1, in2, out));
        out
    }

    pub fn half_adder(&mut self, in1: CircuitVar, in2: CircuitVar) -> CircuitAdderResult {
        CircuitAdderResult {
            out: self.xor(in1, in2),
            carry: self.and(in1, in2),
        }
    }

    pub fn full_adder(
        &mut self,
        in1: CircuitVar,
        in2: CircuitVar,
        carry: CircuitVar,
    ) -> CircuitAdderResult {
        let r1 = self.half_adder(in1, in2);
        let r2 = self.half_adder(r1.out, carry);
        CircuitAdderResult {
            out: r2.out,
            carry: self.or(r1.carry, r2.carry),
        }
    }

    pub fn multiplier(
        &mut self,
        mut lhs_bits: Vec<CircuitVar>,
        mut rhs_bits: Vec<CircuitVar>,
    ) -> Vec<CircuitVar> {
        lhs_bits.reverse();
        rhs_bits.reverse();
        let mut result: Vec<Option<CircuitVar>> = Vec::new();
        let result_len;
        if lhs_bits.len() == 1 && rhs_bits.len() == 1 {
            result_len = 1;
        } else {
            result_len = lhs_bits.len() + rhs_bits.len();
        }
        let add_in_result = move |circuit: &mut Circuit,
                                  result: &mut Vec<Option<CircuitVar>>,
                                  mut pos: usize,
                                  mut x: CircuitVar| {
            loop {
                if pos >= result_len {
                    break;
                }
                while result.len() <= pos {
                    result.push(None);
                }
                let out;
                let carry_op;
                if let Some(ref z) = result[pos] {
                    let CircuitAdderResult { out: o, carry: c } = circuit.half_adder(*z, x);
                    out = o;
                    carry_op = Some(c);
                } else {
                    out = x;
                    carry_op = None;
                }
                result[pos] = Some(out);
                if let Some(carry) = carry_op {
                    x = carry;
                    pos += 1;
                } else {
                    break;
                }
            }
        };
        for i in 0..rhs_bits.len() {
            for j in 0..lhs_bits.len() {
                let pos = i + j;
                let x = self.and(lhs_bits[j], rhs_bits[i]);
                add_in_result(self, &mut result, pos, x);
            }
        }
        let mut result2: Vec<CircuitVar> = result.iter().filter_map(|x| *x).collect();
        result2.reverse();
        result2
    }

    pub fn not_eq_to_one_lsb(&mut self, n: &Vec<CircuitVar>) -> CircuitVar {
        let mut r = n[0];
        for i in 1..n.len() {
            let tmp = self.not(n[i]);
            r = self.and(r, tmp);
        }
        self.not(r)
    }

    pub fn lte_lsb(&mut self, a: &Vec<CircuitVar>, b: &Vec<CircuitVar>) -> CircuitVar {
        let mut r = self.imp(a[0], b[0]);
        for i in 1..min(a.len(), b.len()) {
            let tmp1 = self.not(a[i]);
            let tmp2 = self.and(b[i], tmp1);
            let tmp3 = self.eq(a[i], b[i]);
            let tmp4 = self.and(tmp3, r);
            r = self.or(tmp2, tmp4);
        }
        for i in min(a.len(), b.len())..a.len() {
            let tmp = self.not(a[i]);
            r = self.and(tmp, r);
        }
        for i in min(a.len(), b.len())..b.len() {
            r = self.or(b[i], r);
        }
        r
    }

    pub fn to_cnf(&self) -> CNF {
        let var_to_name = |c: &Circuit, v: &CircuitVar| -> String {
            if let Some(ref var_name) = c.var_names.get(&v.id) {
                (*var_name).clone()
            } else {
                format!("unnamed_{}", v.id)
            }
        };
        let ands: Vec<Vec<(String, bool)>> = self
            .gates
            .iter()
            .flat_map(|gate| {
                match gate {
                    &CircuitGate::And(ref in1, ref in2, ref out) => {
                        let in1_name = var_to_name(self, in1);
                        let in2_name = var_to_name(self, in2);
                        let out_name = var_to_name(self, out);
                        // (out <-> in1 & in2)
                        // (out -> in1 & in2) & (in1 & in2 -> out)
                        // (!out | in1 & in2) & (!in1 | !in2 | out)
                        // (!out | in1) & (!out | in2) & (!in1 | !in2 | out)
                        // {!out,in1},{!out,in2},{!in1,!in2,out}
                        vec![
                            vec![(out_name.clone(), true), (in1_name.clone(), false)],
                            vec![(out_name.clone(), true), (in2_name.clone(), false)],
                            vec![(in1_name, true), (in2_name, true), (out_name, false)],
                        ]
                    }
                    &CircuitGate::Or(ref in1, ref in2, ref out) => {
                        let in1_name = var_to_name(self, in1);
                        let in2_name = var_to_name(self, in2);
                        let out_name = var_to_name(self, out);
                        // (out <-> in1 | in2)
                        // (out -> in1 | in2) & (in1 | in2 -> out)
                        // (!out | in1 | in2) & (!in1 & !in2 | out)
                        // (!out | in1 | in2) & (!in1 | out) & (!in2 | out)
                        // {!out,in1,in2},{!in1,out},{!in2,out}
                        vec![
                            vec![
                                (out_name.clone(), true),
                                (in1_name.clone(), false),
                                (in2_name.clone(), false),
                            ],
                            vec![(in1_name.clone(), true), (out_name.clone(), false)],
                            vec![(in2_name, true), (out_name, false)],
                        ]
                    }
                    &CircuitGate::Not(ref in_, ref out) => {
                        let in_name = var_to_name(self, in_);
                        let out_name = var_to_name(self, out);
                        // (out <-> !in)
                        // (out -> !in) & (!in -> out)
                        // (!out | !in) & (in | out)
                        // {!out,!in},{in,out}
                        vec![
                            vec![(out_name.clone(), true), (in_name.clone(), true)],
                            vec![(in_name, false), (out_name, false)],
                        ]
                    }
                    &CircuitGate::Xor(ref in1, ref in2, ref out) => {
                        let in1_name = var_to_name(self, in1);
                        let in2_name = var_to_name(self, in2);
                        let out_name = var_to_name(self, out);
                        // (out <-> in1 ^ in2)
                        // (out -> in1 ^ in2) & (in1 ^ in2 -> out)
                        // (!out | (in1 & !in2) | (!in1 & in2)) & ((!in1 & !in2) | (in1 & in2) | out)
                        // (!out | (in1 | in2) & (!in1 | !in2)) & ((!in1 | in2) & (in1 | !in2) | out)
                        // (!out | in1 | in2) & (!out | !in1 | !in2) & (out | !in1 | in2) & (out | in1 | !in2)
                        // {!out,in1,in2},{!out,!in1,!in2},{out,!in1,in2},{out,in1,!in2}
                        vec![
                            vec![
                                (out_name.clone(), true),
                                (in1_name.clone(), false),
                                (in2_name.clone(), false),
                            ],
                            vec![
                                (out_name.clone(), true),
                                (in1_name.clone(), true),
                                (in2_name.clone(), true),
                            ],
                            vec![
                                (out_name.clone(), false),
                                (in1_name.clone(), true),
                                (in2_name.clone(), false),
                            ],
                            vec![(out_name, false), (in1_name, false), (in2_name, true)],
                        ]
                    }
                    &CircuitGate::Imp(ref in1, ref in2, ref out) => {
                        let in1_name = var_to_name(self, in1);
                        let in2_name = var_to_name(self, in2);
                        let out_name = var_to_name(self, out);
                        // (out <-> in1 -> in2)
                        // (out <-> !in1 | in2)
                        // (out -> !in1 | in2) & (!in1 | in2 -> out)
                        // (!out | !in1 | in2) & (in1 & !in2 | out)
                        // (!out | !in1 | in2) & (in1 | out) & (!in2 | out)
                        // {!out,!in1,in2},{in1,out},{!in2,out}
                        vec![
                            vec![
                                (out_name.clone(), true),
                                (in1_name.clone(), true),
                                (in2_name.clone(), false),
                            ],
                            vec![(in1_name.clone(), false), (out_name.clone(), false)],
                            vec![(in2_name, true), (out_name, false)],
                        ]
                    }
                    &CircuitGate::Eq(ref in1, ref in2, ref out) => {
                        let in1_name = var_to_name(self, in1);
                        let in2_name = var_to_name(self, in2);
                        let out_name = var_to_name(self, out);
                        // (out <-> in1 <-> in2)
                        // (out <-> (!in1 & !in2) | (in1 & in2))
                        // (out <-> (!in1 | in2) & (in1 | !in2))
                        // (out -> (!in1 | in2) & (in1 | !in2)) & ((!in1 | in2) & (in1 | !in2) -> out)
                        // (!out | (!in1 | in2) & (in1 | !in2)) & (!(!in1 | in2) | !(in1 | !in2) | out)
                        // (!out | (!in1 | in2) & (in1 | !in2)) & ((in1 & !in2) | (!in1 & in2) | out)
                        // (!out | !in1 | in2) & (!out | in1 | !in2) & ((in1 | in2) & (!in1 | !in2) | out)
                        // (!out | !in1 | in2) & (!out | in1 | !in2) & (out | in1 | in2) & (out | !in1 | !in2)
                        // {!out,!in1,in2},{!out,in1,!in2},{out,in1,in2},{out,!in1,!in2}
                        vec![
                            vec![
                                (out_name.clone(), true),
                                (in1_name.clone(), true),
                                (in2_name.clone(), false),
                            ],
                            vec![
                                (out_name.clone(), true),
                                (in1_name.clone(), false),
                                (in2_name.clone(), true),
                            ],
                            vec![
                                (out_name.clone(), false),
                                (in1_name.clone(), false),
                                (in2_name.clone(), false),
                            ],
                            vec![(out_name, false), (in1_name, true), (in2_name, true)],
                        ]
                    }
                }
            })
            .collect();
        CNF { ands }
    }

    pub fn to_sat(&self) -> Sat {
        let clauses: Vec<Vec<isize>> = self
            .gates
            .iter()
            .flat_map(|gate| {
                match gate {
                    &CircuitGate::And(ref in1, ref in2, ref out) => {
                        let in1 = in1.id as isize;
                        let in2 = in2.id as isize;
                        let out = out.id as isize;
                        // (out <-> in1 & in2)
                        // (out -> in1 & in2) & (in1 & in2 -> out)
                        // (!out | in1 & in2) & (!in1 | !in2 | out)
                        // (!out | in1) & (!out | in2) & (!in1 | !in2 | out)
                        // {!out,in1},{!out,in2},{!in1,!in2,out}
                        vec![vec![-out, in1], vec![-out, in2], vec![-in1, -in2, out]]
                    }
                    &CircuitGate::Or(ref in1, ref in2, ref out) => {
                        let in1 = in1.id as isize;
                        let in2 = in2.id as isize;
                        let out = out.id as isize;
                        // (out <-> in1 | in2)
                        // (out -> in1 | in2) & (in1 | in2 -> out)
                        // (!out | in1 | in2) & (!in1 & !in2 | out)
                        // (!out | in1 | in2) & (!in1 | out) & (!in2 | out)
                        // {!out,in1,in2},{!in1,out},{!in2,out}
                        vec![vec![-out, in1, in2], vec![-in1, out], vec![-in2, out]]
                    }
                    &CircuitGate::Not(ref in_, ref out) => {
                        let in_ = in_.id as isize;
                        let out = out.id as isize;
                        // (out <-> !in)
                        // (out -> !in) & (!in -> out)
                        // (!out | !in) & (in | out)
                        // {!out,!in},{in,out}
                        vec![vec![-out, -in_], vec![in_, out]]
                    }
                    &CircuitGate::Xor(ref in1, ref in2, ref out) => {
                        let in1 = in1.id as isize;
                        let in2 = in2.id as isize;
                        let out = out.id as isize;
                        // (out <-> in1 ^ in2)
                        // (out -> in1 ^ in2) & (in1 ^ in2 -> out)
                        // (!out | (in1 & !in2) | (!in1 & in2)) & ((!in1 & !in2) | (in1 & in2) | out)
                        // (!out | (in1 | in2) & (!in1 | !in2)) & ((!in1 | in2) & (in1 | !in2) | out)
                        // (!out | in1 | in2) & (!out | !in1 | !in2) & (out | !in1 | in2) & (out | in1 | !in2)
                        // {!out,in1,in2},{!out,!in1,!in2},{out,!in1,in2},{out,in1,!in2}
                        vec![
                            vec![-out, in1, in2],
                            vec![-out, -in1, -in2],
                            vec![out, -in1, in2],
                            vec![out, in1, -in2],
                        ]
                    }
                    &CircuitGate::Imp(ref in1, ref in2, ref out) => {
                        let in1 = in1.id as isize;
                        let in2 = in2.id as isize;
                        let out = out.id as isize;
                        // (out <-> in1 -> in2)
                        // (out <-> !in1 | in2)
                        // (out -> !in1 | in2) & (!in1 | in2 -> out)
                        // (!out | !in1 | in2) & (in1 & !in2 | out)
                        // (!out | !in1 | in2) & (in1 | out) & (!in2 | out)
                        // {!out,!in1,in2},{in1,out},{!in2,out}
                        vec![vec![-out, -in1, in2], vec![in1, out], vec![-in2, out]]
                    }
                    &CircuitGate::Eq(ref in1, ref in2, ref out) => {
                        let in1 = in1.id as isize;
                        let in2 = in2.id as isize;
                        let out = out.id as isize;
                        // (out <-> in1 <-> in2)
                        // (out <-> (!in1 & !in2) | (in1 & in2))
                        // (out <-> (!in1 | in2) & (in1 | !in2))
                        // (out -> (!in1 | in2) & (in1 | !in2)) & ((!in1 | in2) & (in1 | !in2) -> out)
                        // (!out | (!in1 | in2) & (in1 | !in2)) & (!(!in1 | in2) | !(in1 | !in2) | out)
                        // (!out | (!in1 | in2) & (in1 | !in2)) & ((in1 & !in2) | (!in1 & in2) | out)
                        // (!out | !in1 | in2) & (!out | in1 | !in2) & ((in1 | in2) & (!in1 | !in2) | out)
                        // (!out | !in1 | in2) & (!out | in1 | !in2) & (out | in1 | in2) & (out | !in1 | !in2)
                        // {!out,!in1,in2},{!out,in1,!in2},{out,in1,in2},{out,!in1,!in2}
                        vec![
                            vec![-out, -in1, in2],
                            vec![-out, in1, -in2],
                            vec![out, in1, in2],
                            vec![out, -in1, -in2],
                        ]
                    }
                }
            })
            .collect();
        Sat::from_clauses(clauses)
    }

    pub fn to_3sat(&self) -> _3Sat {
        let clauses: Vec<[isize; 3]> = self
            .gates
            .iter()
            .flat_map(|gate| {
                match gate {
                    &CircuitGate::And(ref in1, ref in2, ref out) => {
                        let in1 = in1.id as isize;
                        let in2 = in2.id as isize;
                        let out = out.id as isize;
                        // (out <-> in1 & in2)
                        // (out -> in1 & in2) & (in1 & in2 -> out)
                        // (!out | in1 & in2) & (!in1 | !in2 | out)
                        // (!out | in1) & (!out | in2) & (!in1 | !in2 | out)
                        // {!out,in1},{!out,in2},{!in1,!in2,out}
                        vec![[-out, in1, in1], [-out, in2, in2], [-in1, -in2, out]]
                    }
                    &CircuitGate::Or(ref in1, ref in2, ref out) => {
                        let in1 = in1.id as isize;
                        let in2 = in2.id as isize;
                        let out = out.id as isize;
                        // (out <-> in1 | in2)
                        // (out -> in1 | in2) & (in1 | in2 -> out)
                        // (!out | in1 | in2) & (!in1 & !in2 | out)
                        // (!out | in1 | in2) & (!in1 | out) & (!in2 | out)
                        // {!out,in1,in2},{!in1,out},{!in2,out}
                        vec![[-out, in1, in2], [-in1, out, out], [-in2, out, out]]
                    }
                    &CircuitGate::Not(ref in_, ref out) => {
                        let in_ = in_.id as isize;
                        let out = out.id as isize;
                        // (out <-> !in)
                        // (out -> !in) & (!in -> out)
                        // (!out | !in) & (in | out)
                        // {!out,!in},{in,out}
                        vec![[-out, -in_, -in_], [in_, out, out]]
                    }
                    &CircuitGate::Xor(ref in1, ref in2, ref out) => {
                        let in1 = in1.id as isize;
                        let in2 = in2.id as isize;
                        let out = out.id as isize;
                        // (out <-> in1 ^ in2)
                        // (out -> in1 ^ in2) & (in1 ^ in2 -> out)
                        // (!out | (in1 & !in2) | (!in1 & in2)) & ((!in1 & !in2) | (in1 & in2) | out)
                        // (!out | (in1 | in2) & (!in1 | !in2)) & ((!in1 | in2) & (in1 | !in2) | out)
                        // (!out | in1 | in2) & (!out | !in1 | !in2) & (out | !in1 | in2) & (out | in1 | !in2)
                        // {!out,in1,in2},{!out,!in1,!in2},{out,!in1,in2},{out,in1,!in2}
                        vec![
                            [-out, in1, in2],
                            [-out, -in1, -in2],
                            [out, -in1, in2],
                            [out, in1, -in2],
                        ]
                    }
                    &CircuitGate::Imp(ref in1, ref in2, ref out) => {
                        let in1 = in1.id as isize;
                        let in2 = in2.id as isize;
                        let out = out.id as isize;
                        // (out <-> in1 -> in2)
                        // (out <-> !in1 | in2)
                        // (out -> !in1 | in2) & (!in1 | in2 -> out)
                        // (!out | !in1 | in2) & (in1 & !in2 | out)
                        // (!out | !in1 | in2) & (in1 | out) & (!in2 | out)
                        // {!out,!in1,in2},{in1,out},{!in2,out}
                        vec![[-out, -in1, in2], [in1, out, out], [-in2, out, out]]
                    }
                    &CircuitGate::Eq(ref in1, ref in2, ref out) => {
                        let in1 = in1.id as isize;
                        let in2 = in2.id as isize;
                        let out = out.id as isize;
                        // (out <-> in1 <-> in2)
                        // (out <-> (!in1 & !in2) | (in1 & in2))
                        // (out <-> (!in1 | in2) & (in1 | !in2))
                        // (out -> (!in1 | in2) & (in1 | !in2)) & ((!in1 | in2) & (in1 | !in2) -> out)
                        // (!out | (!in1 | in2) & (in1 | !in2)) & (!(!in1 | in2) | !(in1 | !in2) | out)
                        // (!out | (!in1 | in2) & (in1 | !in2)) & ((in1 & !in2) | (!in1 & in2) | out)
                        // (!out | !in1 | in2) & (!out | in1 | !in2) & ((in1 | in2) & (!in1 | !in2) | out)
                        // (!out | !in1 | in2) & (!out | in1 | !in2) & (out | in1 | in2) & (out | !in1 | !in2)
                        // {!out,!in1,in2},{!out,in1,!in2},{out,in1,in2},{out,!in1,!in2}
                        vec![
                            [-out, -in1, in2],
                            [-out, in1, -in2],
                            [out, in1, in2],
                            [out, -in1, -in2],
                        ]
                    }
                }
            })
            .collect();
        _3Sat::from_clauses(clauses)
    }

    pub fn to_anf(&self) -> Option<Anf> {
        let var_to_name = |c: &Circuit, v: &CircuitVar| -> String {
            if let Some(ref var_name) = c.var_names.get(&v.id) {
                (*var_name).clone()
            } else {
                format!("unnamed_{}", v.id)
            }
        };
        self.gates.iter().fold(
            None as Option<Anf>,
            |current_op: Option<Anf>, gate: &CircuitGate| {
                let next: Anf;
                match gate {
                    &CircuitGate::And(ref in1, ref in2, ref out) => {
                        let in1_name = var_to_name(self, in1);
                        let in2_name = var_to_name(self, in2);
                        let out_name = var_to_name(self, out);
                        next = Anf::var(in1_name)
                            .and(Anf::var(in2_name))
                            .eq(Anf::var(out_name));
                    }
                    &CircuitGate::Or(ref in1, ref in2, ref out) => {
                        let in1_name = var_to_name(self, in1);
                        let in2_name = var_to_name(self, in2);
                        let out_name = var_to_name(self, out);
                        next = Anf::var(in1_name)
                            .or(Anf::var(in2_name))
                            .eq(Anf::var(out_name));
                    }
                    &CircuitGate::Not(ref in_, ref out) => {
                        let in_name = var_to_name(self, in_);
                        let out_name = var_to_name(self, out);
                        next = Anf::var(in_name).not().eq(Anf::var(out_name));
                    }
                    &CircuitGate::Xor(ref in1, ref in2, ref out) => {
                        let in1_name = var_to_name(self, in1);
                        let in2_name = var_to_name(self, in2);
                        let out_name = var_to_name(self, out);
                        next = Anf::var(in1_name)
                            .xor(Anf::var(in2_name))
                            .eq(Anf::var(out_name));
                    }
                    &CircuitGate::Imp(ref in1, ref in2, ref out) => {
                        let in1_name = var_to_name(self, in1);
                        let in2_name = var_to_name(self, in2);
                        let out_name = var_to_name(self, out);
                        next = Anf::var(in1_name)
                            .imp(Anf::var(in2_name))
                            .eq(Anf::var(out_name));
                    }
                    &CircuitGate::Eq(ref in1, ref in2, ref out) => {
                        let in1_name = var_to_name(self, in1);
                        let in2_name = var_to_name(self, in2);
                        let out_name = var_to_name(self, out);
                        next = Anf::var(in1_name)
                            .eq(Anf::var(in2_name))
                            .eq(Anf::var(out_name));
                    }
                }
                if let Some(current) = current_op {
                    Some(current.and(next))
                } else {
                    Some(next)
                }
            },
        )
    }
}

impl fmt::Display for Circuit {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let var_to_name = |c: &Circuit, v: &CircuitVar| -> String {
            if let Some(ref var_name) = c.var_names.get(&v.id) {
                (*var_name).clone()
            } else {
                format!("unnamed_{}", v.id)
            }
        };
        writeln!(formatter, "Circuit {{")?;
        for gate in &self.gates {
            match gate {
                &CircuitGate::And(ref in1, ref in2, ref out) => {
                    let in1_name = var_to_name(self, in1);
                    let in2_name = var_to_name(self, in2);
                    let out_name = var_to_name(self, out);
                    writeln!(formatter, "  {} = {} & {}", out_name, in1_name, in2_name)?;
                }
                &CircuitGate::Or(ref in1, ref in2, ref out) => {
                    let in1_name = var_to_name(self, in1);
                    let in2_name = var_to_name(self, in2);
                    let out_name = var_to_name(self, out);
                    writeln!(formatter, "  {} = {} | {}", out_name, in1_name, in2_name)?;
                }
                &CircuitGate::Not(ref in_, ref out) => {
                    let in_name = var_to_name(self, in_);
                    let out_name = var_to_name(self, out);
                    writeln!(formatter, "  {} = !{}", out_name, in_name)?;
                }
                &CircuitGate::Xor(ref in1, ref in2, ref out) => {
                    let in1_name = var_to_name(self, in1);
                    let in2_name = var_to_name(self, in2);
                    let out_name = var_to_name(self, out);
                    writeln!(formatter, "  {} = {} ^ {}", out_name, in1_name, in2_name)?;
                }
                &CircuitGate::Imp(ref in1, ref in2, ref out) => {
                    let in1_name = var_to_name(self, in1);
                    let in2_name = var_to_name(self, in2);
                    let out_name = var_to_name(self, out);
                    writeln!(formatter, "  {} = {} -> {}", out_name, in1_name, in2_name)?;
                }
                &CircuitGate::Eq(ref in1, ref in2, ref out) => {
                    let in1_name = var_to_name(self, in1);
                    let in2_name = var_to_name(self, in2);
                    let out_name = var_to_name(self, out);
                    writeln!(formatter, "  {} = {} <-> {}", out_name, in1_name, in2_name)?;
                }
            }
        }
        writeln!(formatter, "}}")?;
        Ok(())
    }
}

#[derive(Clone)]
pub enum CircuitGate {
    And(CircuitVar, CircuitVar, CircuitVar),
    Or(CircuitVar, CircuitVar, CircuitVar),
    Not(CircuitVar, CircuitVar),
    Xor(CircuitVar, CircuitVar, CircuitVar),
    Imp(CircuitVar, CircuitVar, CircuitVar),
    Eq(CircuitVar, CircuitVar, CircuitVar),
}

#[derive(Clone, Copy)]
pub struct CircuitVar {
    pub id: usize,
}
