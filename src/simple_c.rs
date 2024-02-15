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
        PointedByQuery(x) <- PointsTo(x, y), PointedByQuery(y);

        // AddrOf-1
        PointsTo(x, y) <- PointsToQuery(x),
            AddrOfStatement(x, y);

        // AddrOf-2
        PointsTo(x, y) <- PointedByQuery(y),
            AddrOfStatement(x, y);

        // Assign-1
        PointsToQuery(y) <- PointsToQuery(x),
            AssignStatement(x, y);

        // Assign-2
        PointsTo(x, z) <- PointsTo(y, z), PointsToQuery(x),
            AssignStatement(x, y);

        // Assign-3
        PointsTo(x, z) <- PointsTo(y, z), PointedByQuery(z),
            AssignStatement(x, y);

        // Load-1
        PointsToQuery(y) <- PointsToQuery(x),
            LoadStatement(x, y);

        // Load-2
        PointsToQuery(z) <- PointsTo(y, z), PointsToQuery(x),
            LoadStatement(x, y);

        // Load-3
        PointsTo(x, u) <- PointsTo(y, z), PointsTo(z, u), PointsToQuery(x),
            LoadStatement(x, y);

        // Load-4
        PointsTo(x, u) <- PointsTo(y, z), PointsTo(z, u), PointedByQuery(u),
            LoadStatement(x, y);

        // Store-1
        PointsToQuery(y) <- PointsTo(x, z), PointsToQuery(z),
            StoreStatement(x, y);

        // Store-2
        PointsTo(z, u) <- PointsTo(x, z), PointsTo(y, u), PointsToQuery(z),
            StoreStatement(x, y);

        // Store-3
        PointsToQuery(x) <- PointsTo(y, u), PointedByQuery(u),
            StoreStatement(x, y);

        // Store-4
        PointsTo(z, u) <- PointsTo(x, z), PointsTo(y, u), PointedByQuery(u),
            StoreStatement(x, y);
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

        @output
        #[derive(Debug)]
        pub struct PointsTo<'a>(pub Var<'a>, pub Var<'a>);

        // AddrOf
        PointsTo(x, y) <-
            AddrOfStatement(x, y);

        // Assign
        PointsTo(x, z) <- PointsTo(y, z),
            AssignStatement(x, y);

        // Load
        PointsTo(x, u) <- PointsTo(y, z), PointsTo(z, u),
            LoadStatement(x, y);

        // Store
        PointsTo(z, u) <- PointsTo(x, z), PointsTo(y, u),
            StoreStatement(x, y);
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

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use quickcheck::Arbitrary;
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

    impl Arbitrary for SimpleCStatement<'static> {
        fn arbitrary(_g: &mut quickcheck::Gen) -> Self {
            panic!("Shouldn't generate like this")
        }
    }

    impl Arbitrary for SimpleCProgram<'static> {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            let num_stmts = g.size();
            let num_vars = g.size() / 5 + 2;
            let variables = get_vars(num_vars);

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
            SimpleCProgram(prog)
        }

        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            Box::new(self.0.shrink().map(SimpleCProgram))
        }
    }

    impl Arbitrary for Query<'static> {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            let num_vars = g.size() / 5 + 2;
            let variables = get_vars(num_vars);
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
    fn correctness(prog: SimpleCProgram<'static>, query: Query<'static>) -> bool {
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
}
