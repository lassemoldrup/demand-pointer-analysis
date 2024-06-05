use std::fmt::{self, Debug, Display, Formatter};

use itertools::Itertools;
use quickcheck::Arbitrary;

use crate::simple_c::get_vars;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Var<'a> {
    name: &'a str,
    offset: u32,
}

impl Display for Var<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}{}", self.name, self.offset)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Query {
    PointsTo(usize),
    PointedBy(usize),
}

impl Arbitrary for Query {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let num_vars = g.size() / 5 + 2;
        let x = *g.choose(&(0..num_vars).collect_vec()).unwrap();
        match *g.choose(&[0, 1]).unwrap() {
            0 => Query::PointsTo(x),
            1 => Query::PointedBy(x),
            _ => panic!("Oh no"),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FieldSensitiveCStatement {
    AddrOf { lhs: usize, rhs: usize },
    Assign { lhs: usize, rhs: usize, offset: u32 },
    Load { lhs: usize, rhs: usize, offset: u32 },
    Store { lhs: usize, rhs: usize, offset: u32 },
}

impl Arbitrary for FieldSensitiveCStatement {
    fn arbitrary(_g: &mut quickcheck::Gen) -> Self {
        panic!("Shouldn't generate like this")
    }
}

impl<'a> Debug for FieldSensitiveCProgram<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for stmt in &self.stmts {
            match stmt {
                FieldSensitiveCStatement::AddrOf { lhs, rhs } => {
                    writeln!(f, "{}  <- &{}", self.vars[*lhs], self.vars[*rhs])?;
                }
                FieldSensitiveCStatement::Assign { lhs, rhs, offset } => {
                    writeln!(f, "{} <- &{}->{offset}", self.vars[*lhs], self.vars[*rhs])?;
                }
                FieldSensitiveCStatement::Load { lhs, rhs, offset } => {
                    writeln!(f, "{} <- {}->{offset}", self.vars[*lhs], self.vars[*rhs])?;
                }
                FieldSensitiveCStatement::Store { lhs, rhs, offset } => {
                    writeln!(f, "{}->{offset} <- {}", self.vars[*lhs], self.vars[*rhs])?;
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone)]
pub struct FieldSensitiveCProgram<'a> {
    pub vars: Vec<Var<'a>>,
    pub stmts: Vec<FieldSensitiveCStatement>,
}

impl FieldSensitiveCProgram<'_> {
    pub fn push(&mut self, stmt: FieldSensitiveCStatement) {
        self.stmts.push(stmt);
    }
}

impl Arbitrary for FieldSensitiveCProgram<'static> {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let num_stmts = g.size();
        let num_vars = g.size() / 5 + 2;
        let mut vars = Vec::with_capacity(num_vars);
        let var_indices = (0..num_vars).collect_vec();
        let mut vars_iter = get_vars(num_vars);
        vars.push(Var {
            name: vars_iter.next().unwrap(),
            offset: 0,
        });
        for i in 1..num_vars {
            if *g.choose(&[0, 1]).unwrap() == 0 {
                vars.push(Var {
                    name: vars_iter.next().unwrap(),
                    offset: 0,
                });
            } else {
                vars.push(Var {
                    name: vars[i - 1].name,
                    offset: vars[i - 1].offset + 1,
                });
            }
        }

        let mut prog = FieldSensitiveCProgram {
            vars,
            stmts: Vec::with_capacity(num_stmts),
        };
        for _ in 0..num_stmts {
            let lhs = *g.choose(&var_indices).unwrap();
            let rhs = *g.choose(&var_indices).unwrap();
            let kind = g.choose(&[0, 1, 2, 3]).unwrap();
            let offset = *g
                .choose(&[
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    1,
                    1,
                    2,
                    2,
                    3,
                    4,
                    6,
                    8,
                    10,
                    num_vars / 2,
                ])
                .unwrap() as u32;
            match kind {
                0 => prog.push(FieldSensitiveCStatement::AddrOf { lhs, rhs }),
                1 => prog.push(FieldSensitiveCStatement::Assign { lhs, rhs, offset }),
                2 => prog.push(FieldSensitiveCStatement::Load { lhs, rhs, offset }),
                3 => prog.push(FieldSensitiveCStatement::Store { lhs, rhs, offset }),
                _ => panic!("Oh no"),
            }
        }
        prog
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let vars = self.vars.clone();
        Box::new(self.stmts.shrink().map(move |stmts| Self {
            vars: vars.clone(),
            stmts,
        }))
    }
}

pub mod demand {
    use std::collections::HashSet;

    use super::*;

    crepe::crepe! {
        @input
        struct InPointsToQuery(usize);
        @input
        struct InPointedByQuery(usize);

        @input
        struct AddrOfStatement(usize, usize);

        @input
        struct AssignStatement(usize, usize, u32);

        @input
        struct LoadStatement(usize, usize, u32);

        @input
        struct StoreStatement(usize, usize, u32);

        @input
        struct Omega(usize, u32);

        struct Copy(usize, usize, u32);

        @output
        #[derive(Debug)]
        pub struct PointsTo(pub usize, pub usize);

        @output
        #[derive(Debug)]
        pub struct PointsToQuery(pub usize);
        @output
        #[derive(Debug)]
        pub struct PointedByQuery(pub usize);

        PointsToQuery(x) <- InPointsToQuery(x);
        PointedByQuery(x) <- InPointedByQuery(x);

        // Flip
        PointedByQuery(x) <- PointsToQuery(x);
        // Chain
        PointedByQuery(x) <- PointsTo(x, t), PointedByQuery(t);

        // Offset-Query
        PointedByQuery(t) <- Omega(t, i),
            PointedByQuery(t + i as usize);

        // AddrOf-PT
        PointsTo(x, y) <- PointsToQuery(x),
            AddrOfStatement(x, y);

        // AddrOf-PB
        PointsTo(x, y) <- PointedByQuery(y),
            AddrOfStatement(x, y);

        // Assign
        Copy(y, x, i) <-
            AssignStatement(x, y, i);

        // Load
        Copy(t + i as usize, x, 0) <- PointsTo(y, t),
            LoadStatement(x, y, i),
            Omega(t, i);

        // Load-Query
        PointsToQuery(y) <- PointsToQuery(x),
            LoadStatement(x, y, _);

        // Store
        Copy(y, t + i as usize, 0) <- PointsTo(x, t),
            StoreStatement(x, y, i),
            Omega(t, i);

        // Store-Query
        PointsToQuery(x) <- PointsTo(y, t), PointedByQuery(t),
            StoreStatement(x, y, _);

        // Copy-PT
        PointsTo(x, t + i as usize) <- PointsTo(y, t),
            Copy(y, x, i),
            Omega(t, i),
            PointsToQuery(x);

        // Copy-PB
        PointsTo(x, t + i as usize) <- PointsTo(y, t),
            Copy(y, x, i),
            Omega(t, i),
            PointedByQuery(t + i as usize);

        // Copy-Query
        PointsToQuery(y) <- PointsToQuery(x), Copy(y, x, _);
    }

    pub fn analyze<'a>(
        program: &FieldSensitiveCProgram<'a>,
        queries: impl IntoIterator<Item = Query>,
    ) -> (
        HashSet<PointsTo>,
        HashSet<PointsToQuery>,
        HashSet<PointedByQuery>,
    ) {
        let mut runtime = Crepe::new();

        for &statement in &program.stmts {
            match statement {
                FieldSensitiveCStatement::AddrOf { lhs, rhs } => {
                    runtime.extend([AddrOfStatement(lhs, rhs)])
                }
                FieldSensitiveCStatement::Assign { lhs, rhs, offset } => {
                    runtime.extend([AssignStatement(lhs, rhs, offset)])
                }
                FieldSensitiveCStatement::Load { lhs, rhs, offset } => {
                    runtime.extend([LoadStatement(lhs, rhs, offset)])
                }
                FieldSensitiveCStatement::Store { lhs, rhs, offset } => {
                    runtime.extend([StoreStatement(lhs, rhs, offset)])
                }
            }
        }

        let omegas = program.vars.iter().enumerate().flat_map(|(i, var)| {
            (i.saturating_sub(var.offset as usize)..=i).map(move |j| Omega(j, (i - j) as u32))
        });
        runtime.extend(omegas);

        for query in queries {
            match query {
                Query::PointsTo(x) => runtime.extend([InPointsToQuery(x)]),
                Query::PointedBy(x) => runtime.extend([InPointedByQuery(x)]),
            }
        }

        runtime.run()
    }
}

pub mod exhaustive {
    use std::collections::HashSet;

    use super::*;

    crepe::crepe! {
        @input
        struct AddrOfStatement(usize, usize);

        @input
        struct AssignStatement(usize, usize, u32);

        @input
        struct LoadStatement(usize, usize, u32);

        @input
        struct StoreStatement(usize, usize, u32);

        @input
        struct Omega(usize, u32);

        struct Copy(usize, usize, u32);

        @output
        #[derive(Debug)]
        pub struct PointsTo(pub usize, pub usize);

        // AddrOf
        PointsTo(x, y) <-
            AddrOfStatement(x, y);

        // Assign
        Copy(y, x, i) <-
            AssignStatement(x, y, i);

        // Load
        Copy(t + i as usize, x, 0) <- PointsTo(y, t),
            LoadStatement(x, y, i),
            Omega(t, i);

        // Store
        Copy(y, t + i as usize, 0) <- PointsTo(x, t),
            StoreStatement(x, y, i),
            Omega(t, i);

        // Copy
        PointsTo(x, t + i as usize) <- PointsTo(y, t), Copy(y, x, i),
            Omega(t, i);
    }

    pub fn analyze<'a>(program: &FieldSensitiveCProgram<'a>) -> HashSet<PointsTo> {
        let mut runtime = Crepe::new();

        for &statement in &program.stmts {
            match statement {
                FieldSensitiveCStatement::AddrOf { lhs, rhs } => {
                    runtime.extend([AddrOfStatement(lhs, rhs)])
                }
                FieldSensitiveCStatement::Assign { lhs, rhs, offset } => {
                    runtime.extend([AssignStatement(lhs, rhs, offset)])
                }
                FieldSensitiveCStatement::Load { lhs, rhs, offset } => {
                    runtime.extend([LoadStatement(lhs, rhs, offset)])
                }
                FieldSensitiveCStatement::Store { lhs, rhs, offset } => {
                    runtime.extend([StoreStatement(lhs, rhs, offset)])
                }
            }
        }

        let omegas = program.vars.iter().enumerate().flat_map(|(i, var)| {
            (i.saturating_sub(var.offset as usize)..=i).map(move |j| Omega(j, (i - j) as u32))
        });
        runtime.extend(omegas);

        runtime.run().0
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use quickcheck_macros::quickcheck;

    use super::*;

    #[quickcheck]
    fn demand_driven_correctness(prog: FieldSensitiveCProgram<'static>, query: Query) -> bool {
        let points_to_exhaustive = exhaustive::analyze(&prog);
        let points_to_demand = demand::analyze(&prog, [query]).0;

        match query {
            Query::PointsTo(x) => {
                let exhaustive_pointees: HashSet<_> = points_to_exhaustive
                    .into_iter()
                    .filter_map(|exhaustive::PointsTo(a, b)| (x == a).then_some(b))
                    .collect();
                let demand_pointees: HashSet<_> = points_to_demand
                    .into_iter()
                    .filter_map(|demand::PointsTo(a, b)| (x == a).then_some(b))
                    .collect();
                exhaustive_pointees == demand_pointees
            }
            Query::PointedBy(y) => {
                let exhaustive_pointers: HashSet<_> = points_to_exhaustive
                    .into_iter()
                    .filter_map(|exhaustive::PointsTo(a, b)| (y == b).then_some(a))
                    .collect();
                let demand_pointers: HashSet<_> = points_to_demand
                    .into_iter()
                    .filter_map(|demand::PointsTo(a, b)| (y == b).then_some(a))
                    .collect();
                exhaustive_pointers == demand_pointers
            }
        }
    }

    #[quickcheck]
    fn query_completeness(prog: FieldSensitiveCProgram<'static>, query: Query) -> bool {
        let (points_to, queries_pt, queries_pb) = demand::analyze(&prog, [query]);

        for demand::PointsTo(x, y) in points_to {
            if !queries_pt.contains(&demand::PointsToQuery(x))
                && !queries_pb.contains(&demand::PointedByQuery(y))
            {
                return false;
            }
        }
        true
    }

    #[quickcheck]
    fn exhaustive_satisfies_constraint(prog: FieldSensitiveCProgram<'static>) -> bool {
        use super::exhaustive::*;
        let res = analyze(&prog);
        let points_to_set = |pt| {
            res.iter()
                .filter_map(move |&PointsTo(p, x)| (pt == p).then_some(x))
        };
        prog.stmts.into_iter().all(|stmt| match stmt {
            FieldSensitiveCStatement::AddrOf { lhs, rhs } => res.contains(&PointsTo(lhs, rhs)),
            FieldSensitiveCStatement::Assign { lhs, rhs, offset } => points_to_set(rhs).all(|x| {
                let x2 = x + offset as usize;
                !prog.vars.get(x2).is_some_and(|var| var.offset >= offset)
                    || res.contains(&PointsTo(lhs, x2))
            }),
            FieldSensitiveCStatement::Load { lhs, rhs, offset } => points_to_set(rhs).all(|p| {
                let p2 = p + offset as usize;
                !prog.vars.get(p2).is_some_and(|var| var.offset >= offset)
                    || points_to_set(p2).all(|x| res.contains(&PointsTo(lhs, x)))
            }),
            FieldSensitiveCStatement::Store { lhs, rhs, offset } => points_to_set(lhs).all(|p| {
                let p2 = p + offset as usize;
                !prog.vars.get(p2).is_some_and(|var| var.offset >= offset)
                    || points_to_set(rhs).all(|x| res.contains(&PointsTo(p2, x)))
            }),
        })
    }
}
