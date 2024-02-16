use std::fmt::{self, Display, Formatter};

pub type Var<'a> = &'a str;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum CVar<'a> {
    Var(Var<'a>),
    ObjectField(Term, Var<'a>),
}

pub type Term = usize;

#[macro_export]
macro_rules! simple_java {
    (@ $x:ident <- new $($tt:tt)*) => {
        {
            use $crate::simple_java::SimpleJavaStatement;
            let mut stmts = simple_java!(@ $($tt)*);
            stmts.push(SimpleJavaStatement::New { lhs: stringify!($x) });
            stmts
        }
    };
    (@ $x:ident <- $y:ident.$f:ident $($tt:tt)*) => {
        {
            use $crate::simple_java::SimpleJavaStatement;
            let mut stmts = simple_java!(@ $($tt)*);
            stmts.push(SimpleJavaStatement::Load { lhs: stringify!($x), rhs: stringify!($y), field: stringify!($f) });
            stmts
        }
    };
    (@ $x:ident.$f:ident <- $y:ident $($tt:tt)*) => {
        {
            use $crate::simple_java::SimpleJavaStatement;
            let mut stmts = simple_java!(@ $($tt)*);
            stmts.push(SimpleJavaStatement::Store { lhs: stringify!($x), rhs: stringify!($y), field: stringify!($f) });
            stmts
        }
    };
    (@ $x:ident <- $y:ident $($tt:tt)*) => {
        {
            use $crate::simple_java::SimpleJavaStatement;
            let mut stmts = simple_java!(@ $($tt)*);
            stmts.push(SimpleJavaStatement::Assign { lhs: stringify!($x), rhs: stringify!($y) });
            stmts
        }
    };
    (@) => {
        {
            use $crate::simple_java::SimpleJavaProgram;
            SimpleJavaProgram(Vec::new())
        }
    };
    ($($tt:tt)*) => {
        {
            let mut stmts = simple_java!(@ $($tt)*);
            stmts.0.reverse();
            stmts
        }
    };
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum SimpleJavaStatement<'a> {
    New {
        lhs: Var<'a>,
    },
    Assign {
        lhs: Var<'a>,
        rhs: Var<'a>,
    },
    Load {
        lhs: Var<'a>,
        rhs: Var<'a>,
        field: Var<'a>,
    },
    Store {
        lhs: Var<'a>,
        rhs: Var<'a>,
        field: Var<'a>,
    },
}

#[derive(Clone, Debug)]
pub struct SimpleJavaProgram<'a>(pub Vec<SimpleJavaStatement<'a>>);

impl<'a> SimpleJavaProgram<'a> {
    pub fn push(&mut self, stmt: SimpleJavaStatement<'a>) {
        self.0.push(stmt);
    }
}

impl<'a> Display for SimpleJavaStatement<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            SimpleJavaStatement::New { lhs } => write!(f, "{lhs}   <- new"),
            SimpleJavaStatement::Assign { lhs, rhs } => write!(f, "{lhs}   <- {rhs}"),
            SimpleJavaStatement::Load { lhs, rhs, field } => write!(f, "{lhs}   <- {rhs}.{field}"),
            SimpleJavaStatement::Store { lhs, rhs, field } => write!(f, "{lhs}.{field} <- {rhs}"),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Query<'a> {
    PointsTo(Var<'a>),
    PointedBy(Term),
}

pub mod demand {
    use std::collections::HashSet;

    use super::*;

    crepe::crepe! {
        @input
        struct InPointsToQuery<'a>(CVar<'a>);
        @input
        struct InPointedByQuery(Term);

        @input
        struct NewStatement<'a>(CVar<'a>, Term);

        @input
        struct AssignStatement<'a>(CVar<'a>, CVar<'a>);

        @input
        struct LoadStatement<'a>(CVar<'a>, CVar<'a>, Var<'a>);

        @input
        struct StoreStatement<'a>(CVar<'a>, CVar<'a>, Var<'a>);

        @output
        #[derive(Debug)]
        pub struct PointsTo<'a>(pub CVar<'a>, pub Term);

        @output
        #[derive(Debug)]
        pub struct PointsToQuery<'a>(pub CVar<'a>);
        @output
        #[derive(Debug)]
        pub struct PointedByQuery(pub Term);

        PointsToQuery(x) <- InPointsToQuery(x);
        PointedByQuery(x) <- InPointedByQuery(x);

        // Flip
        PointedByQuery(o) <- PointsToQuery(x),
            let CVar::ObjectField(o, _) = x;
        // Chain
        PointedByQuery(o) <- PointsTo(x, t), PointedByQuery(t),
            let CVar::ObjectField(o, _) = x;

        // New-1
        PointsTo(x, o) <- PointsToQuery(x),
            NewStatement(x, o);

        // New-2
        PointsTo(x, o) <- PointedByQuery(o),
            NewStatement(x, o);

        // Assign-1
        PointsToQuery(y) <- PointsToQuery(x),
            AssignStatement(x, y);

        // Assign-2
        PointsTo(x, t) <- PointsTo(y, t), PointsToQuery(x),
            AssignStatement(x, y);

        // Assign-3
        PointsTo(x, t) <- PointsTo(y, t), PointedByQuery(t),
            AssignStatement(x, y);

        // Load-1
        PointsToQuery(y) <- PointsToQuery(x),
            LoadStatement(x, y, _);

        // Load-2
        PointsToQuery(CVar::ObjectField(o, f)) <- PointsTo(y, o), PointsToQuery(x),
            LoadStatement(x, y, f);

        // Load-3
        PointsTo(x, t) <- PointsTo(y, o), PointsToQuery(x),
            LoadStatement(x, y, f),
            PointsTo(CVar::ObjectField(o, f), t);

        // Load-4
        PointsTo(x, t) <- PointsTo(y, o), PointedByQuery(t),
            LoadStatement(x, y, f),
            PointsTo(CVar::ObjectField(o, f), t);

        // Store-1
        PointsToQuery(y) <- PointsTo(x, o),
            StoreStatement(x, y, f),
           PointsToQuery(CVar::ObjectField(o, f));

        // Store-2
        PointsTo(CVar::ObjectField(o, f), t) <- PointsTo(x, o), PointsTo(y, t),
            StoreStatement(x, y, f),
            PointsToQuery(CVar::ObjectField(o, f));

        // Store-3
        PointsToQuery(x) <- PointsTo(y, t), PointedByQuery(t),
            StoreStatement(x, y, _);

        // Store-4
        PointsTo(CVar::ObjectField(o, f), t) <- PointsTo(x, o), PointsTo(y, t), PointedByQuery(t),
            StoreStatement(x, y, f);
    }

    pub fn analyze<'a>(
        program: &SimpleJavaProgram<'a>,
        queries: impl IntoIterator<Item = Query<'a>>,
    ) -> (
        HashSet<PointsTo<'a>>,
        HashSet<PointsToQuery<'a>>,
        HashSet<PointedByQuery>,
    ) {
        let mut runtime = Crepe::new();

        for (i, statement) in program.0.iter().enumerate() {
            match statement {
                SimpleJavaStatement::New { lhs } => {
                    runtime.extend([NewStatement(CVar::Var(lhs), i)])
                }
                SimpleJavaStatement::Assign { lhs, rhs } => {
                    runtime.extend([AssignStatement(CVar::Var(lhs), CVar::Var(rhs))])
                }
                SimpleJavaStatement::Load { lhs, rhs, field } => {
                    runtime.extend([LoadStatement(CVar::Var(lhs), CVar::Var(rhs), field)])
                }
                SimpleJavaStatement::Store { lhs, rhs, field } => {
                    runtime.extend([StoreStatement(CVar::Var(lhs), CVar::Var(rhs), field)])
                }
            }
        }

        for query in queries {
            match query {
                Query::PointsTo(x) => runtime.extend([InPointsToQuery(CVar::Var(x))]),
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
        struct NewStatement<'a>(CVar<'a>, Term);

        @input
        struct AssignStatement<'a>(CVar<'a>, CVar<'a>);

        @input
        struct LoadStatement<'a>(CVar<'a>, CVar<'a>, Var<'a>);

        @input
        struct StoreStatement<'a>(CVar<'a>, CVar<'a>, Var<'a>);

        @output
        #[derive(Debug)]
        pub struct PointsTo<'a>(pub CVar<'a>, pub Term);

        // New
        PointsTo(x, o) <-
            NewStatement(x, o);

        // Assign
        PointsTo(x, t) <- PointsTo(y, t),
            AssignStatement(x, y);

        // Load
        PointsTo(x, t) <- PointsTo(y, o),
            LoadStatement(x, y, f),
            PointsTo(CVar::ObjectField(o, f), t);

        // Store
        PointsTo(CVar::ObjectField(o, f), t) <- PointsTo(x, o), PointsTo(y, t),
            StoreStatement(x, y, f);
    }

    pub fn analyze<'a>(program: &SimpleJavaProgram<'a>) -> HashSet<PointsTo<'a>> {
        let mut runtime = Crepe::new();

        for (i, statement) in program.0.iter().enumerate() {
            match statement {
                SimpleJavaStatement::New { lhs } => {
                    runtime.extend([NewStatement(CVar::Var(lhs), i)])
                }
                SimpleJavaStatement::Assign { lhs, rhs } => {
                    runtime.extend([AssignStatement(CVar::Var(lhs), CVar::Var(rhs))])
                }
                SimpleJavaStatement::Load { lhs, rhs, field } => {
                    runtime.extend([LoadStatement(CVar::Var(lhs), CVar::Var(rhs), field)])
                }
                SimpleJavaStatement::Store { lhs, rhs, field } => {
                    runtime.extend([StoreStatement(CVar::Var(lhs), CVar::Var(rhs), field)])
                }
            }
        }

        runtime.run().0
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use quickcheck::{Arbitrary, Gen, QuickCheck};
    use quickcheck_macros::quickcheck;

    use super::*;

    fn get_vars(n: usize) -> Vec<&'static str> {
        ('a'..='z')
            .map(String::from)
            .chain((1..).map(|n| n.to_string()))
            .map(|s| s.leak() as &'static str)
            .take(n)
            .collect()
    }

    impl Arbitrary for SimpleJavaStatement<'static> {
        fn arbitrary(_g: &mut quickcheck::Gen) -> Self {
            panic!("Shouldn't generate like this")
        }
    }

    impl Arbitrary for SimpleJavaProgram<'static> {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            let num_stmts = g.size();
            let num_vars = g.size() / 5 + 2;
            let variables = get_vars(num_vars);

            let mut prog = Vec::with_capacity(num_stmts);
            for _ in 0..num_stmts {
                let lhs = g.choose(&variables).unwrap();
                let rhs = g.choose(&variables).unwrap();
                let field = g.choose(&variables).unwrap();
                let kind = g.choose(&[0, 1, 2, 3]).unwrap();
                match kind {
                    0 => prog.push(SimpleJavaStatement::New { lhs }),
                    1 => prog.push(SimpleJavaStatement::Assign { lhs, rhs }),
                    2 => prog.push(SimpleJavaStatement::Load { lhs, rhs, field }),
                    3 => prog.push(SimpleJavaStatement::Store { lhs, rhs, field }),
                    _ => panic!("Oh no"),
                }
            }
            SimpleJavaProgram(prog)
        }

        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            Box::new(self.0.shrink().map(SimpleJavaProgram))
        }
    }

    #[derive(Clone, Debug)]
    struct SimpleJavaProgAndQuery(SimpleJavaProgram<'static>, Query<'static>);

    impl Arbitrary for SimpleJavaProgAndQuery {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            let prog = SimpleJavaProgram::arbitrary(g);
            let new_idxs: Vec<_> = prog
                .0
                .iter()
                .enumerate()
                .filter_map(|(i, s)| match s {
                    SimpleJavaStatement::New { .. } => Some(i),
                    _ => None,
                })
                .collect();

            let num_vars = g.size() / 5 + 2;
            let variables = get_vars(num_vars);
            let var = g.choose(&variables).unwrap();
            let Some(&new_idx) = g.choose(&new_idxs) else {
                return SimpleJavaProgAndQuery(prog, Query::PointsTo(var));
            };

            let kind = g.choose(&[0, 1]).unwrap();
            let query = if *kind == 0 {
                Query::PointsTo(var)
            } else {
                Query::PointedBy(new_idx)
            };
            SimpleJavaProgAndQuery(prog, query)
        }

        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            let q = self.1;
            Box::new(self.0.shrink().map(move |p| SimpleJavaProgAndQuery(p, q)))
        }
    }

    #[test]
    fn exhaustive_assignment_chain() {
        let my_program = simple_java! {
            a <- new
            b <- a
        };

        assert_eq!(
            HashSet::from([
                exhaustive::PointsTo(CVar::Var("a"), 0),
                exhaustive::PointsTo(CVar::Var("b"), 0)
            ]),
            super::exhaustive::analyze(&my_program)
        );
    }

    #[test]
    fn exhaustive_store() {
        let my_program = simple_java! {
            a <- new
            b <- new
            c <- new
            b <- c
            b.f <- a
        };

        assert_eq!(
            HashSet::from([
                exhaustive::PointsTo(CVar::Var("a"), 0),
                exhaustive::PointsTo(CVar::Var("b"), 1),
                exhaustive::PointsTo(CVar::Var("b"), 2),
                exhaustive::PointsTo(CVar::Var("c"), 2),
                exhaustive::PointsTo(CVar::ObjectField(1, "f"), 0),
                exhaustive::PointsTo(CVar::ObjectField(2, "f"), 0),
            ]),
            super::exhaustive::analyze(&my_program)
        );
    }

    #[test]
    fn exhaustive_load() {
        let my_program = simple_java! {
            a <- new
            b <- new
            c <- new
            b <- c
            b.f <- a
            d <- b.f
            e <- b.f
        };

        assert_eq!(
            HashSet::from([
                exhaustive::PointsTo(CVar::Var("a"), 0),
                exhaustive::PointsTo(CVar::Var("b"), 1),
                exhaustive::PointsTo(CVar::Var("b"), 2),
                exhaustive::PointsTo(CVar::Var("c"), 2),
                exhaustive::PointsTo(CVar::Var("d"), 0),
                exhaustive::PointsTo(CVar::Var("e"), 0),
                exhaustive::PointsTo(CVar::ObjectField(1, "f"), 0),
                exhaustive::PointsTo(CVar::ObjectField(2, "f"), 0),
            ]),
            super::exhaustive::analyze(&my_program)
        );
    }

    #[test]
    fn exhaustive_satisfies_constraint() {
        fn inner(prog: SimpleJavaProgram<'static>) -> bool {
            use super::exhaustive::*;
            let res = analyze(&prog);
            let points_to_set = |pt| {
                res.iter()
                    .filter_map(move |&PointsTo(p, x)| (pt == p).then_some(x))
            };
            prog.0.into_iter().enumerate().all(|(i, stmt)| match stmt {
                SimpleJavaStatement::New { lhs } => res.contains(&PointsTo(CVar::Var(lhs), i)),
                SimpleJavaStatement::Assign { lhs, rhs } => points_to_set(CVar::Var(rhs))
                    .all(|x| res.contains(&PointsTo(CVar::Var(lhs), x))),
                SimpleJavaStatement::Load { lhs, rhs, field } => {
                    points_to_set(CVar::Var(rhs)).all(|o| {
                        points_to_set(CVar::ObjectField(o, field))
                            .all(|x| res.contains(&PointsTo(CVar::Var(lhs), x)))
                    })
                }
                SimpleJavaStatement::Store { lhs, rhs, field } => points_to_set(CVar::Var(lhs))
                    .all(|o| {
                        points_to_set(CVar::Var(rhs))
                            .all(|x| res.contains(&PointsTo(CVar::ObjectField(o, field), x)))
                    }),
            })
        }

        QuickCheck::new()
            .gen(Gen::new(40))
            .quickcheck(inner as fn(SimpleJavaProgram<'static>) -> bool);
    }

    #[test]
    fn demand_driven_equals_exhaustive() {
        fn inner(SimpleJavaProgAndQuery(prog, query): SimpleJavaProgAndQuery) -> bool {
            let points_to_exhaustive = exhaustive::analyze(&prog);
            let points_to_demand = demand::analyze(&prog, [query]).0;

            match query {
                Query::PointsTo(x) => {
                    let exhaustive_pointees: HashSet<_> = points_to_exhaustive
                        .into_iter()
                        .filter_map(|exhaustive::PointsTo(a, b)| (CVar::Var(x) == a).then_some(b))
                        .collect();
                    let demand_pointees: HashSet<_> = points_to_demand
                        .into_iter()
                        .filter_map(|demand::PointsTo(a, b)| (CVar::Var(x) == a).then_some(b))
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

        QuickCheck::new()
            .gen(Gen::new(40))
            .quickcheck(inner as fn(SimpleJavaProgAndQuery) -> bool);
    }
}
