use std::fmt::{self, Display, Formatter};

pub type Var<'a> = &'a str;

macro_rules! simple_c {
    ($x:ident <- $y:ident $($tt:tt)*) => {
        simple_c!($($tt)*)
    };
    () => {
        Vec::new()
    };
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum SimpleCStatement<'a> {
    AddrOf { lhs: Var<'a>, rhs: Var<'a> },
    Assign { lhs: Var<'a>, rhs: Var<'a> },
    Load { lhs: Var<'a>, rhs: Var<'a> },
    Store { lhs: Var<'a>, rhs: Var<'a> },
}

pub type SimpleCProgram<'a> = Vec<SimpleCStatement<'a>>;

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

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Query<'a> {
    PointsTo(Var<'a>),
    PointedBy(Var<'a>),
}

pub mod demand {
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
        struct PointsTo<'a>(Var<'a>, Var<'a>);

        @output
        #[derive(Debug)]
        struct PointsToQuery<'a>(Var<'a>);
        @output
        #[derive(Debug)]
        struct PointedByQuery<'a>(Var<'a>);

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

    pub fn analyze<'a>(program: SimpleCProgram<'a>, queries: impl IntoIterator<Item = Query<'a>>) {
        let mut runtime = Crepe::new();

        for statement in program {
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

        let (points_to, points_to_queries, pointed_by_queries) = runtime.run();
        println!("{points_to:?}");
        println!("{points_to_queries:?}");
        println!("{pointed_by_queries:?}");
    }
}
