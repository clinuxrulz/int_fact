use std::fmt;
use std::ops::{Index, IndexMut};

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Lit {
    x: isize,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Var {
    x: isize,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct CnfClause {
    x: CnfClauseData,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum CnfClauseData {
    L0,
    L1(Lit),
    L2(Lit, Lit),
    L3(Lit, Lit, Lit),
    LN(Vec<Lit>),
}

pub struct CnfClauseIter<'a> {
    target: &'a CnfClause,
    idx: usize,
}

pub struct CnfClauseIterMut<'a> {
    target: &'a mut CnfClause,
    idx: usize,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct CnfFormula {
    clauses: Vec<CnfClause>,
}

impl Lit {
    pub fn var(&self) -> Var {
        Var { x: self.x.abs() }
    }

    pub fn is_negated(&self) -> bool {
        self.x < 0
    }

    pub fn negated(self) -> Lit {
        Lit { x: -self.x }
    }
}

impl From<isize> for Lit {
    fn from(x: isize) -> Lit {
        Lit { x }
    }
}

impl Into<isize> for Lit {
    fn into(self) -> isize {
        self.x
    }
}

impl From<isize> for Var {
    fn from(x: isize) -> Var {
        Var { x }
    }
}

impl Into<isize> for Var {
    fn into(self) -> isize {
        self.x
    }
}

impl CnfClause {
    fn panic_ioob(&self, idx: usize) -> ! {
        panic!("index was {}, but length is {}", idx, self.len());
    }

    fn bounds_check(&self, idx: usize) {
        if idx >= self.len() {
            self.panic_ioob(idx);
        }
    }

    pub fn new() -> CnfClause {
        CnfClause {
            x: CnfClauseData::L0,
        }
    }

    pub fn clear(&mut self) {
        self.x = CnfClauseData::L0;
    }

    pub fn push<L: Into<Lit>>(&mut self, lit: L) {
        let lit: Lit = lit.into();
        let x = match &mut self.x {
            &mut CnfClauseData::L0 => CnfClauseData::L1(lit),
            &mut CnfClauseData::L1(x0) => CnfClauseData::L2(x0, lit),
            &mut CnfClauseData::L2(x0, x1) => CnfClauseData::L3(x0, x1, lit),
            &mut CnfClauseData::L3(x0, x1, x2) => CnfClauseData::LN(vec![x0, x1, x2, lit]),
            &mut CnfClauseData::LN(ref mut x) => {
                let mut x2: Vec<Lit> = Vec::new();
                std::mem::swap(&mut x2, x);
                x2.push(lit);
                CnfClauseData::LN(x2)
            }
        };
        self.x = x;
    }

    pub fn retain<P: FnMut(&Lit) -> bool>(&mut self, mut pred: P) {
        let x_op = match &mut self.x {
            &mut CnfClauseData::LN(ref mut x) => {
                x.retain(|lit| pred(lit));
                if x.len() <= 3 {
                    let mut x2 = CnfClause::new();
                    for x3 in x {
                        x2.push(*x3);
                    }
                    Some(x2.x)
                } else {
                    let mut x2: Vec<Lit> = Vec::new();
                    std::mem::swap(&mut x2, x);
                    Some(CnfClauseData::LN(x2))
                }
            }
            _ => None,
        };
        if let Some(x) = x_op {
            self.x = x;
            return;
        }
        let mut x2 = CnfClause::new();
        for x in &*self {
            if pred(x) {
                x2.push(*x);
            }
        }
        self.x = x2.x;
    }

    pub fn remove(&mut self, idx: usize) -> Lit {
        let r = self[idx];
        let mut at: usize = 0;
        self.retain(|_| {
            let tmp = at;
            at += 1;
            tmp != idx
        });
        r
    }

    pub fn sort_by<Cmp: FnMut(&Lit, &Lit) -> std::cmp::Ordering>(&mut self, mut cmp: Cmp) {
        match &mut self.x {
            &mut CnfClauseData::L0 => {}
            &mut CnfClauseData::L1(_) => {}
            &mut CnfClauseData::L2(ref mut x0, ref mut x1) => {
                if cmp(x0, x1) == std::cmp::Ordering::Greater {
                    std::mem::swap(x0, x1);
                }
            }
            &mut CnfClauseData::L3(ref mut x0, ref mut x1, ref mut x2) => {
                if cmp(x0, x1) == std::cmp::Ordering::Greater {
                    std::mem::swap(x0, x1);
                }
                if cmp(x1, x2) == std::cmp::Ordering::Greater {
                    std::mem::swap(x1, x2);
                }
                if cmp(x0, x1) == std::cmp::Ordering::Greater {
                    std::mem::swap(x0, x1);
                }
            }
            &mut CnfClauseData::LN(ref mut x) => {
                x.sort_by(cmp);
            }
        }
    }

    pub fn simplify(&mut self) {
        // remove duplicates
        self.sort_by(|a, b| {
            let x: isize = (*a).into();
            let y: isize = (*b).into();
            x.cmp(&y)
        });
        for i in (1..self.len()).rev() {
            if self[i] == self[i - 1] {
                self.remove(i);
            }
        }
        // check for tautology
        self.sort_by(|a, b| {
            let x: isize = (*a).into();
            let y: isize = (*b).into();
            x.abs().cmp(&y.abs())
        });
        if !self.is_empty() {
            for i in 0..self.len() - 1 {
                for j in i + 1..self.len() {
                    if self[j] == self[i].negated() {
                        self.clear();
                        return;
                    }
                }
            }
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn len(&self) -> usize {
        match &self.x {
            &CnfClauseData::L0 => 0,
            &CnfClauseData::L1(_) => 1,
            &CnfClauseData::L2(_, _) => 2,
            &CnfClauseData::L3(_, _, _) => 3,
            &CnfClauseData::LN(ref x) => x.len(),
        }
    }
}

impl<L: Into<Lit>> From<L> for CnfClause {
    fn from(x0: L) -> CnfClause {
        CnfClause {
            x: CnfClauseData::L1(x0.into()),
        }
    }
}

impl<L1: Into<Lit>, L2: Into<Lit>> From<(L1, L2)> for CnfClause {
    fn from((x0, x1): (L1, L2)) -> CnfClause {
        CnfClause {
            x: CnfClauseData::L2(x0.into(), x1.into()),
        }
    }
}

impl<L1: Into<Lit>, L2: Into<Lit>, L3: Into<Lit>> From<(L1, L2, L3)> for CnfClause {
    fn from((x0, x1, x2): (L1, L2, L3)) -> CnfClause {
        CnfClause {
            x: CnfClauseData::L3(x0.into(), x1.into(), x2.into()),
        }
    }
}

impl<L: Into<Lit>> From<Vec<L>> for CnfClause {
    fn from(x: Vec<L>) -> CnfClause {
        let mut r = CnfClause::new();
        for x2 in x {
            r.push(x2);
        }
        r
    }
}

impl<C: Into<CnfClause>> From<Vec<C>> for CnfFormula {
    fn from(clauses: Vec<C>) -> CnfFormula {
        let mut clauses2 = Vec::with_capacity(clauses.len());
        for clause in clauses {
            clauses2.push(clause.into());
        }
        CnfFormula { clauses: clauses2 }
    }
}

impl Index<usize> for CnfClause {
    type Output = Lit;

    fn index(&self, idx: usize) -> &Lit {
        self.bounds_check(idx);
        match &self.x {
            &CnfClauseData::L0 => {
                unreachable!();
            }
            &CnfClauseData::L1(ref x0) => match idx {
                0 => x0,
                _ => unreachable!(),
            },
            &CnfClauseData::L2(ref x0, ref x1) => match idx {
                0 => x0,
                1 => x1,
                _ => unreachable!(),
            },
            &CnfClauseData::L3(ref x0, ref x1, ref x2) => match idx {
                0 => x0,
                1 => x1,
                2 => x2,
                _ => unreachable!(),
            },
            &CnfClauseData::LN(ref x) => &x[idx],
        }
    }
}

impl IndexMut<usize> for CnfClause {
    fn index_mut(&mut self, idx: usize) -> &mut Lit {
        self.bounds_check(idx);
        match &mut self.x {
            &mut CnfClauseData::L0 => {
                unreachable!();
            }
            &mut CnfClauseData::L1(ref mut x0) => match idx {
                0 => x0,
                _ => unreachable!(),
            },
            &mut CnfClauseData::L2(ref mut x0, ref mut x1) => match idx {
                0 => x0,
                1 => x1,
                _ => unreachable!(),
            },
            &mut CnfClauseData::L3(ref mut x0, ref mut x1, ref mut x2) => match idx {
                0 => x0,
                1 => x1,
                2 => x2,
                _ => unreachable!(),
            },
            &mut CnfClauseData::LN(ref mut x) => &mut x[idx],
        }
    }
}

impl Index<usize> for CnfFormula {
    type Output = CnfClause;

    fn index(&self, idx: usize) -> &CnfClause {
        &self.clauses[idx]
    }
}

impl IndexMut<usize> for CnfFormula {
    fn index_mut(&mut self, idx: usize) -> &mut CnfClause {
        &mut self.clauses[idx]
    }
}

impl<'a> IntoIterator for &'a CnfClause {
    type Item = &'a Lit;
    type IntoIter = CnfClauseIter<'a>;

    fn into_iter(self) -> CnfClauseIter<'a> {
        CnfClauseIter::new(self, 0)
    }
}

impl<'a> IntoIterator for &'a mut CnfClause {
    type Item = &'a mut Lit;
    type IntoIter = CnfClauseIterMut<'a>;

    fn into_iter(self) -> CnfClauseIterMut<'a> {
        CnfClauseIterMut::new(self, 0)
    }
}

impl<'a> CnfClauseIter<'a> {
    fn new(target: &'a CnfClause, idx: usize) -> Self {
        CnfClauseIter { target, idx }
    }
}

impl<'a> Iterator for CnfClauseIter<'a> {
    type Item = &'a Lit;

    fn next(&mut self) -> Option<&'a Lit> {
        if self.idx < self.target.len() {
            let idx = self.idx;
            self.idx += 1;
            Some(&self.target[idx])
        } else {
            None
        }
    }
}

impl<'a> CnfClauseIterMut<'a> {
    fn new(target: &'a mut CnfClause, idx: usize) -> Self {
        CnfClauseIterMut { target, idx }
    }
}

impl<'a> Iterator for CnfClauseIterMut<'a> {
    type Item = &'a mut Lit;

    fn next(&mut self) -> Option<&'a mut Lit> {
        if self.idx < self.target.len() {
            let idx = self.idx;
            self.idx += 1;
            let target: *mut CnfClause = self.target;
            let target2: &'a mut CnfClause = unsafe { &mut *target };
            Some(&mut target2[idx])
        } else {
            None
        }
    }
}

impl<'a> IntoIterator for &'a CnfFormula {
    type Item = &'a CnfClause;
    type IntoIter = std::slice::Iter<'a, CnfClause>;

    fn into_iter(self) -> Self::IntoIter {
        self.clauses.iter()
    }
}

impl<'a> IntoIterator for &'a mut CnfFormula {
    type Item = &'a mut CnfClause;
    type IntoIter = std::slice::IterMut<'a, CnfClause>;

    fn into_iter(self) -> Self::IntoIter {
        self.clauses.iter_mut()
    }
}

impl fmt::Display for CnfFormula {
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
                let lit2: isize = (*lit).into();
                write!(formatter, "{}", lit2)?;
            }
            write!(formatter, "}}")?;
        }
        Ok(())
    }
}

impl CnfFormula {
    pub fn new() -> CnfFormula {
        CnfFormula {
            clauses: Vec::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    pub fn clear(&mut self) {
        self.clauses.clear();
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    pub fn insert<C:Into<CnfClause>>(&mut self, idx: usize, clause: C) {
        self.clauses.insert(idx, clause.into());
    }

    pub fn remove(&mut self, idx: usize) -> CnfClause {
        self.clauses.remove(idx)
    }

    pub fn push<C:Into<CnfClause>>(&mut self, clause: C) {
        self.clauses.push(clause.into());
    }

    pub fn assign_lit(&mut self, lit: Lit) {
        for i in (0..self.len()).rev() {
            if self[i].into_iter().any(|lit2:&Lit| *lit2 == lit) {
                self.remove(i);
            } else {
                self[i].retain(|lit2| *lit2 != lit.negated());
                if self[i].is_empty() {
                    self.clear();
                    self.push(CnfClause::new());
                    return;
                }
            }
        }
    }

    pub fn duel(&self) -> DnfFormula {
        let mut dnf = DnfFormula::new();
        for clause in self {
            let mut clause2 = DnfClause::new();
            for lit in clause {
                clause2.push(lit.negated());
            }
            dnf.push(clause2);
        }
        dnf
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct DnfClause {
    x: DnfClauseData,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum DnfClauseData {
    L0,
    L1(Lit),
    L2(Lit, Lit),
    L3(Lit, Lit, Lit),
    LN(Vec<Lit>),
}

pub struct DnfClauseIter<'a> {
    target: &'a DnfClause,
    idx: usize,
}

pub struct DnfClauseIterMut<'a> {
    target: &'a mut DnfClause,
    idx: usize,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct DnfFormula {
    clauses: Vec<DnfClause>,
}

impl DnfClause {
    fn panic_ioob(&self, idx: usize) -> ! {
        panic!("index was {}, but length is {}", idx, self.len());
    }

    fn bounds_check(&self, idx: usize) {
        if idx >= self.len() {
            self.panic_ioob(idx);
        }
    }

    pub fn new() -> DnfClause {
        DnfClause {
            x: DnfClauseData::L0,
        }
    }

    pub fn clear(&mut self) {
        self.x = DnfClauseData::L0;
    }

    pub fn push<L: Into<Lit>>(&mut self, lit: L) {
        let lit: Lit = lit.into();
        let x = match &mut self.x {
            &mut DnfClauseData::L0 => DnfClauseData::L1(lit),
            &mut DnfClauseData::L1(x0) => DnfClauseData::L2(x0, lit),
            &mut DnfClauseData::L2(x0, x1) => DnfClauseData::L3(x0, x1, lit),
            &mut DnfClauseData::L3(x0, x1, x2) => DnfClauseData::LN(vec![x0, x1, x2, lit]),
            &mut DnfClauseData::LN(ref mut x) => {
                let mut x2: Vec<Lit> = Vec::new();
                std::mem::swap(&mut x2, x);
                x2.push(lit);
                DnfClauseData::LN(x2)
            }
        };
        self.x = x;
    }

    pub fn retain<P: FnMut(&Lit) -> bool>(&mut self, mut pred: P) {
        let x_op = match &mut self.x {
            &mut DnfClauseData::LN(ref mut x) => {
                x.retain(|lit| pred(lit));
                if x.len() <= 3 {
                    let mut x2 = DnfClause::new();
                    for x3 in x {
                        x2.push(*x3);
                    }
                    Some(x2.x)
                } else {
                    let mut x2: Vec<Lit> = Vec::new();
                    std::mem::swap(&mut x2, x);
                    Some(DnfClauseData::LN(x2))
                }
            }
            _ => None,
        };
        if let Some(x) = x_op {
            self.x = x;
            return;
        }
        let mut x2 = DnfClause::new();
        for x in &*self {
            if pred(x) {
                x2.push(*x);
            }
        }
        self.x = x2.x;
    }

    pub fn remove(&mut self, idx: usize) -> Lit {
        let r = self[idx];
        let mut at: usize = 0;
        self.retain(|_| {
            let tmp = at;
            at += 1;
            tmp != idx
        });
        r
    }

    pub fn sort_by<Cmp: FnMut(&Lit, &Lit) -> std::cmp::Ordering>(&mut self, mut cmp: Cmp) {
        match &mut self.x {
            &mut DnfClauseData::L0 => {}
            &mut DnfClauseData::L1(_) => {}
            &mut DnfClauseData::L2(ref mut x0, ref mut x1) => {
                if cmp(x0, x1) == std::cmp::Ordering::Greater {
                    std::mem::swap(x0, x1);
                }
            }
            &mut DnfClauseData::L3(ref mut x0, ref mut x1, ref mut x2) => {
                if cmp(x0, x1) == std::cmp::Ordering::Greater {
                    std::mem::swap(x0, x1);
                }
                if cmp(x1, x2) == std::cmp::Ordering::Greater {
                    std::mem::swap(x1, x2);
                }
                if cmp(x0, x1) == std::cmp::Ordering::Greater {
                    std::mem::swap(x0, x1);
                }
            }
            &mut DnfClauseData::LN(ref mut x) => {
                x.sort_by(cmp);
            }
        }
    }

    pub fn simplify(&mut self) {
        // remove duplicates
        self.sort_by(|a, b| {
            let x: isize = (*a).into();
            let y: isize = (*b).into();
            x.cmp(&y)
        });
        for i in (1..self.len()).rev() {
            if self[i] == self[i - 1] {
                self.remove(i);
            }
        }
        // check for contradiction
        self.sort_by(|a, b| {
            let x: isize = (*a).into();
            let y: isize = (*b).into();
            x.abs().cmp(&y.abs())
        });
        if !self.is_empty() {
            for i in 0..self.len() - 1 {
                for j in i + 1..self.len() {
                    if self[j] == self[i].negated() {
                        self.clear();
                        return;
                    }
                }
            }
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn len(&self) -> usize {
        match &self.x {
            &DnfClauseData::L0 => 0,
            &DnfClauseData::L1(_) => 1,
            &DnfClauseData::L2(_, _) => 2,
            &DnfClauseData::L3(_, _, _) => 3,
            &DnfClauseData::LN(ref x) => x.len(),
        }
    }
}

impl<L: Into<Lit>> From<L> for DnfClause {
    fn from(x0: L) -> DnfClause {
        DnfClause {
            x: DnfClauseData::L1(x0.into()),
        }
    }
}

impl<L1: Into<Lit>, L2: Into<Lit>> From<(L1, L2)> for DnfClause {
    fn from((x0, x1): (L1, L2)) -> DnfClause {
        DnfClause {
            x: DnfClauseData::L2(x0.into(), x1.into()),
        }
    }
}

impl<L1: Into<Lit>, L2: Into<Lit>, L3: Into<Lit>> From<(L1, L2, L3)> for DnfClause {
    fn from((x0, x1, x2): (L1, L2, L3)) -> DnfClause {
        DnfClause {
            x: DnfClauseData::L3(x0.into(), x1.into(), x2.into()),
        }
    }
}

impl<L: Into<Lit>> From<Vec<L>> for DnfClause {
    fn from(x: Vec<L>) -> DnfClause {
        let mut r = DnfClause::new();
        for x2 in x {
            r.push(x2);
        }
        r
    }
}

impl<C: Into<DnfClause>> From<Vec<C>> for DnfFormula {
    fn from(clauses: Vec<C>) -> DnfFormula {
        let mut clauses2 = Vec::with_capacity(clauses.len());
        for clause in clauses {
            clauses2.push(clause.into());
        }
        DnfFormula { clauses: clauses2 }
    }
}

impl Index<usize> for DnfClause {
    type Output = Lit;

    fn index(&self, idx: usize) -> &Lit {
        self.bounds_check(idx);
        match &self.x {
            &DnfClauseData::L0 => {
                unreachable!();
            }
            &DnfClauseData::L1(ref x0) => match idx {
                0 => x0,
                _ => unreachable!(),
            },
            &DnfClauseData::L2(ref x0, ref x1) => match idx {
                0 => x0,
                1 => x1,
                _ => unreachable!(),
            },
            &DnfClauseData::L3(ref x0, ref x1, ref x2) => match idx {
                0 => x0,
                1 => x1,
                2 => x2,
                _ => unreachable!(),
            },
            &DnfClauseData::LN(ref x) => &x[idx],
        }
    }
}

impl IndexMut<usize> for DnfClause {
    fn index_mut(&mut self, idx: usize) -> &mut Lit {
        self.bounds_check(idx);
        match &mut self.x {
            &mut DnfClauseData::L0 => {
                unreachable!();
            }
            &mut DnfClauseData::L1(ref mut x0) => match idx {
                0 => x0,
                _ => unreachable!(),
            },
            &mut DnfClauseData::L2(ref mut x0, ref mut x1) => match idx {
                0 => x0,
                1 => x1,
                _ => unreachable!(),
            },
            &mut DnfClauseData::L3(ref mut x0, ref mut x1, ref mut x2) => match idx {
                0 => x0,
                1 => x1,
                2 => x2,
                _ => unreachable!(),
            },
            &mut DnfClauseData::LN(ref mut x) => &mut x[idx],
        }
    }
}

impl Index<usize> for DnfFormula {
    type Output = DnfClause;

    fn index(&self, idx: usize) -> &DnfClause {
        &self.clauses[idx]
    }
}

impl IndexMut<usize> for DnfFormula {
    fn index_mut(&mut self, idx: usize) -> &mut DnfClause {
        &mut self.clauses[idx]
    }
}

impl<'a> IntoIterator for &'a DnfClause {
    type Item = &'a Lit;
    type IntoIter = DnfClauseIter<'a>;

    fn into_iter(self) -> DnfClauseIter<'a> {
        DnfClauseIter::new(self, 0)
    }
}

impl<'a> IntoIterator for &'a mut DnfClause {
    type Item = &'a mut Lit;
    type IntoIter = DnfClauseIterMut<'a>;

    fn into_iter(self) -> DnfClauseIterMut<'a> {
        DnfClauseIterMut::new(self, 0)
    }
}

impl<'a> DnfClauseIter<'a> {
    fn new(target: &'a DnfClause, idx: usize) -> Self {
        DnfClauseIter { target, idx }
    }
}

impl<'a> Iterator for DnfClauseIter<'a> {
    type Item = &'a Lit;

    fn next(&mut self) -> Option<&'a Lit> {
        if self.idx < self.target.len() {
            let idx = self.idx;
            self.idx += 1;
            Some(&self.target[idx])
        } else {
            None
        }
    }
}

impl<'a> DnfClauseIterMut<'a> {
    fn new(target: &'a mut DnfClause, idx: usize) -> Self {
        DnfClauseIterMut { target, idx }
    }
}

impl<'a> Iterator for DnfClauseIterMut<'a> {
    type Item = &'a mut Lit;

    fn next(&mut self) -> Option<&'a mut Lit> {
        if self.idx < self.target.len() {
            let idx = self.idx;
            self.idx += 1;
            let target: *mut DnfClause = self.target;
            let target2: &'a mut DnfClause = unsafe { &mut *target };
            Some(&mut target2[idx])
        } else {
            None
        }
    }
}

impl<'a> IntoIterator for &'a DnfFormula {
    type Item = &'a DnfClause;
    type IntoIter = std::slice::Iter<'a, DnfClause>;

    fn into_iter(self) -> Self::IntoIter {
        self.clauses.iter()
    }
}

impl<'a> IntoIterator for &'a mut DnfFormula {
    type Item = &'a mut DnfClause;
    type IntoIter = std::slice::IterMut<'a, DnfClause>;

    fn into_iter(self) -> Self::IntoIter {
        self.clauses.iter_mut()
    }
}

impl fmt::Display for DnfFormula {
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
                let lit2: isize = (*lit).into();
                write!(formatter, "{}", lit2)?;
            }
            write!(formatter, "}}")?;
        }
        Ok(())
    }
}

impl DnfFormula {
    pub fn new() -> DnfFormula {
        DnfFormula {
            clauses: Vec::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    pub fn clear(&mut self) {
        self.clauses.clear();
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    pub fn append(&mut self, other: &mut DnfFormula) {
        self.clauses.append(&mut other.clauses);
    }

    pub fn sort(&mut self) {
        self.clauses.sort();
    }

    pub fn dedup(&mut self) {
        self.clauses.dedup();
    }

    pub fn insert<C:Into<DnfClause>>(&mut self, idx: usize, clause: C) {
        self.clauses.insert(idx, clause.into());
    }

    pub fn remove(&mut self, idx: usize) -> DnfClause {
        self.clauses.remove(idx)
    }

    pub fn push<C:Into<DnfClause>>(&mut self, clause: C) {
        self.clauses.push(clause.into());
    }

    pub fn assign_lit(&mut self, lit: Lit) {
        for i in (0..self.len()).rev() {
            if self[i].into_iter().any(|lit2:&Lit| *lit2 == lit.negated()) {
                self.remove(i);
            } else {
                self[i].retain(|lit2| *lit2 != lit);
                if self[i].is_empty() {
                    self.clear();
                    self.push(DnfClause::new());
                    return;
                }
            }
        }
    }

    pub fn duel(&self) -> CnfFormula {
        let mut cnf = CnfFormula::new();
        for clause in self {
            let mut clause2 = CnfClause::new();
            for lit in clause {
                clause2.push(lit.negated());
            }
            cnf.push(clause2);
        }
        cnf
    }
}

