use std::fmt::{self, Display, Formatter};

pub type Var<'a> = &'a str;

#[macro_export]
macro_rules! simple_c {
    ($x:ident <- &$y:ident $($tt:tt)*) => {
        {
            use $crate::simple_c::SimpleCStatement;
            let mut stmts = simple_c!($($tt)*);
            stmts.push(SimpleCStatement::AddrOf { lhs: stringify!($x), rhs: stringify!($y) });
            stmts
        }
    };
    ($x:ident <- $y:ident $($tt:tt)*) => {
        {
            use $crate::simple_c::SimpleCStatement;
            let mut stmts = simple_c!($($tt)*);
            stmts.push(SimpleCStatement::Assign { lhs: stringify!($x), rhs: stringify!($y) });
            stmts
        }
    };
    ($x:ident <- *$y:ident $($tt:tt)*) => {
        {
            use $crate::simple_c::SimpleCStatement;
            let mut stmts = simple_c!($($tt)*);
            stmts.push(SimpleCStatement::Load { lhs: stringify!($x), rhs: stringify!($y) });
            stmts
        }
    };
    (*$x:ident <- $y:ident $($tt:tt)*) => {
        {
            use $crate::simple_c::SimpleCStatement;
            let mut stmts = simple_c!($($tt)*);
            stmts.push(SimpleCStatement::Store { lhs: stringify!($x), rhs: stringify!($y) });
            stmts
        }
    };
    () => {
        {
            use $crate::simple_c::SimpleCProgram;
            SimpleCProgram(Vec::new())
        }
    };
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum SimpleCStatement<'a> {
    AddrOf { lhs: Var<'a>, rhs: Var<'a> },
    Assign { lhs: Var<'a>, rhs: Var<'a> },
    Load { lhs: Var<'a>, rhs: Var<'a> },
    Store { lhs: Var<'a>, rhs: Var<'a> },
}

#[derive(Clone, Debug)]
pub struct SimpleCProgram<'a>(pub Vec<SimpleCStatement<'a>>);

impl<'a> SimpleCProgram<'a> {
    pub fn push(&mut self, stmt: SimpleCStatement<'a>) {
        self.0.push(stmt);
    }
}

impl<'a> Display for SimpleCStatement<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            SimpleCStatement::AddrOf { lhs, rhs } => write!(f, "{lhs}  <- &{rhs}"),
            SimpleCStatement::Assign { lhs, rhs } => write!(f, "{lhs}  <-  {rhs}"),
            SimpleCStatement::Load { lhs, rhs } => write!(f, "{lhs}  <- *{rhs}"),
            SimpleCStatement::Store { lhs, rhs } => write!(f, "*{lhs} <-  {rhs}"),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Query<'a> {
    PointsTo(Var<'a>),
    PointedBy(Var<'a>),
}

pub mod demand {
    use std::collections::HashSet;

    use super::*;

    crepe::crepe! {
        @input
        struct InPointsToQuery<'a>(Var<'a>);
        @input
        struct InPointedByQuery<'a>(Var<'a>);

        @input
        struct AddrOfStatement<'a>(Var<'a>, Var<'a>);

        @input
        struct AssignStatement<'a>(Var<'a>, Var<'a>);

        @input
        struct LoadStatement<'a>(Var<'a>, Var<'a>);

        @input
        struct StoreStatement<'a>(Var<'a>, Var<'a>);

        struct Copy<'a>(Var<'a>, Var<'a>);

        @output
        #[derive(Debug)]
        pub struct PointsTo<'a>(pub Var<'a>, pub Var<'a>);

        @output
        #[derive(Debug)]
        pub struct PointsToQuery<'a>(pub Var<'a>);
        @output
        #[derive(Debug)]
        pub struct PointedByQuery<'a>(pub Var<'a>);

        PointsToQuery(x) <- InPointsToQuery(x);
        PointedByQuery(x) <- InPointedByQuery(x);

        // Flip
        PointedByQuery(x) <- PointsToQuery(x);
        // Chain
        PointedByQuery(x) <- PointsTo(x, t), PointedByQuery(t);

        // AddrOf-PT
        PointsTo(x, y) <- PointsToQuery(x),
            AddrOfStatement(x, y);

        // AddrOf-PB
        PointsTo(x, y) <- PointedByQuery(y),
            AddrOfStatement(x, y);

        // Assign
        Copy(y, x) <- AssignStatement(x, y);

        // Load
        Copy(t, x) <- PointsTo(y, t),
            LoadStatement(x, y);

        // Load-Query
        PointsToQuery(y) <- PointsToQuery(x),
            LoadStatement(x, y);

        // Store
        Copy(y, t) <- PointsTo(x, t),
            StoreStatement(x, y);

        // Store-Query
        PointsToQuery(x) <- PointsTo(y, t), PointedByQuery(t),
            StoreStatement(x, y);

        // Copy-PT
        PointsTo(x, t) <- PointsTo(y, t), Copy(y, x), PointsToQuery(x);

        // Copy-PB
        PointsTo(x, t) <- PointsTo(y, t), Copy(y, x), PointedByQuery(t);

        // Copy-Query
        PointsToQuery(y) <- PointsToQuery(x), Copy(y, x);
    }

    pub fn analyze<'a>(
        program: &SimpleCProgram<'a>,
        queries: impl IntoIterator<Item = Query<'a>>,
    ) -> (
        HashSet<PointsTo<'a>>,
        HashSet<PointsToQuery<'a>>,
        HashSet<PointedByQuery<'a>>,
    ) {
        let mut runtime = Crepe::new();

        for statement in &program.0 {
            match statement {
                SimpleCStatement::AddrOf { lhs, rhs } => {
                    runtime.extend([AddrOfStatement(lhs, rhs)])
                }
                SimpleCStatement::Assign { lhs, rhs } => {
                    runtime.extend([AssignStatement(lhs, rhs)])
                }
                SimpleCStatement::Load { lhs, rhs } => runtime.extend([LoadStatement(lhs, rhs)]),
                SimpleCStatement::Store { lhs, rhs } => runtime.extend([StoreStatement(lhs, rhs)]),
            }
        }

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
        struct AddrOfStatement<'a>(Var<'a>, Var<'a>);

        @input
        struct AssignStatement<'a>(Var<'a>, Var<'a>);

        @input
        struct LoadStatement<'a>(Var<'a>, Var<'a>);

        @input
        struct StoreStatement<'a>(Var<'a>, Var<'a>);

        struct Copy<'a>(Var<'a>, Var<'a>);

        @output
        #[derive(Debug)]
        pub struct PointsTo<'a>(pub Var<'a>, pub Var<'a>);

        // AddrOf
        PointsTo(x, y) <-
            AddrOfStatement(x, y);

        // Assign
        Copy(y, x) <-
            AssignStatement(x, y);

        // Load
        Copy(t, x) <- PointsTo(y, t),
            LoadStatement(x, y);

        // Store
        Copy(y, t) <- PointsTo(x, t),
            StoreStatement(x, y);

        // Copy
        PointsTo(x, t) <- PointsTo(y, t), Copy(y, x);
    }

    pub fn analyze<'a>(program: &SimpleCProgram<'a>) -> HashSet<PointsTo<'a>> {
        let mut runtime = Crepe::new();

        for statement in &program.0 {
            match statement {
                SimpleCStatement::AddrOf { lhs, rhs } => {
                    runtime.extend([AddrOfStatement(lhs, rhs)])
                }
                SimpleCStatement::Assign { lhs, rhs } => {
                    runtime.extend([AssignStatement(lhs, rhs)])
                }
                SimpleCStatement::Load { lhs, rhs } => runtime.extend([LoadStatement(lhs, rhs)]),
                SimpleCStatement::Store { lhs, rhs } => runtime.extend([StoreStatement(lhs, rhs)]),
            }
        }

        runtime.run().0
    }
}

pub fn get_vars(n: usize) -> impl Iterator<Item = &'static str> {
    ('a'..='z')
        .map(String::from)
        .chain((1..).map(|n| n.to_string()))
        .map(|s| s.leak() as &'static str)
        .take(n)
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use itertools::Itertools;
    use quickcheck::Arbitrary;
    use quickcheck_macros::quickcheck;

    use super::*;
    impl Arbitrary for SimpleCStatement<'static> {
        fn arbitrary(_g: &mut quickcheck::Gen) -> Self {
            panic!("Shouldn't generate like this")
        }
    }

    impl Arbitrary for SimpleCProgram<'static> {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            let num_stmts = g.size();
            let num_vars = g.size() / 5 + 2;
            let variables = get_vars(num_vars).collect_vec();

            let mut prog = Vec::with_capacity(num_stmts);
            for _ in 0..num_stmts {
                let lhs = g.choose(&variables).unwrap();
                let rhs = g.choose(&variables).unwrap();
                let kind = g.choose(&[0, 1, 2, 3]).unwrap();
                match kind {
                    0 => prog.push(SimpleCStatement::AddrOf { lhs, rhs }),
                    1 => prog.push(SimpleCStatement::Assign { lhs, rhs }),
                    2 => prog.push(SimpleCStatement::Load { lhs, rhs }),
                    3 => prog.push(SimpleCStatement::Store { lhs, rhs }),
                    _ => panic!("Oh no"),
                }
            }
            Self(prog)
        }

        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            Box::new(self.0.shrink().map(Self))
        }
    }

    impl Arbitrary for Query<'static> {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            let num_vars = g.size() / 5 + 2;
            let variables = get_vars(num_vars).collect_vec();
            let var = g.choose(&variables).unwrap();
            let kind = g.choose(&[0, 1]).unwrap();
            if *kind == 0 {
                Query::PointsTo(var)
            } else {
                Query::PointedBy(var)
            }
        }
    }

    #[quickcheck]
    fn demand_driven_correctness(prog: SimpleCProgram<'static>, query: Query<'static>) -> bool {
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
    fn query_completeness(prog: SimpleCProgram<'static>, query: Query<'static>) -> bool {
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

    #[test]
    fn exhaustive_assignment_chain() {
        let prog = simple_c! {
            s <- &y
            p <- &x
            q <- p
            r <- q
        };
        let res = exhaustive::analyze(&prog);
        assert!(res.contains(&exhaustive::PointsTo("r", "x")));
        assert!(!res.contains(&exhaustive::PointsTo("r", "y")));
    }

    #[test]
    fn exhaustive_store() {
        let prog = simple_c! {
            p  <- &x
            q  <- &p
            yp <- &y
            *q <- yp
        };
        let res = exhaustive::analyze(&prog);
        assert!(res.contains(&exhaustive::PointsTo("p", "x")));
        assert!(res.contains(&exhaustive::PointsTo("p", "y")));
        assert!(!res.contains(&exhaustive::PointsTo("p", "p")));
    }

    #[test]
    fn exhaustive_load() {
        let prog = simple_c! {
            p <- &x
            q <- &p
            r <- *q
        };
        let res = exhaustive::analyze(&prog);
        assert!(res.contains(&exhaustive::PointsTo("r", "x")));
        assert!(!res.contains(&exhaustive::PointsTo("r", "p")));
    }

    #[quickcheck]
    fn exhaustive_satisfies_constraint(prog: SimpleCProgram<'static>) -> bool {
        use super::exhaustive::*;
        let res = analyze(&prog);
        let points_to_set = |pt| {
            res.iter()
                .filter_map(move |&PointsTo(p, x)| (pt == p).then_some(x))
        };
        prog.0.into_iter().all(|stmt| match stmt {
            SimpleCStatement::AddrOf { lhs, rhs } => res.contains(&PointsTo(lhs, rhs)),
            SimpleCStatement::Assign { lhs, rhs } => {
                points_to_set(rhs).all(|x| res.contains(&PointsTo(lhs, x)))
            }
            SimpleCStatement::Load { lhs, rhs } => points_to_set(rhs)
                .all(|p| points_to_set(p).all(|x| res.contains(&PointsTo(lhs, x)))),
            SimpleCStatement::Store { lhs, rhs } => points_to_set(lhs)
                .all(|p| points_to_set(rhs).all(|x| res.contains(&PointsTo(p, x)))),
        })
    }
}
