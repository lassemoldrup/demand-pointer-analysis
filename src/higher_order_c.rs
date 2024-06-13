use std::fmt::{self, Debug, Display, Formatter};

use quickcheck::Arbitrary;

pub type Var<'a> = &'a str;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Ident<'a> {
    Var(Var<'a>),
    Param(Var<'a>),
    Return(Var<'a>),
    Function(Var<'a>),
}

impl<'a> Ident<'a> {
    pub fn name(self) -> Var<'a> {
        match self {
            Self::Var(v) | Self::Param(v) | Self::Return(v) | Self::Function(v) => v,
        }
    }

    pub fn is_function(self) -> bool {
        matches!(self, Self::Function(_))
    }
}

impl<'a> Display for Ident<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Var(v) => write!(f, "{}", v),
            Self::Param(v) => write!(f, "p_{}", v),
            Self::Return(v) => write!(f, "r_{}", v),
            Self::Function(v) => write!(f, "λ_{}", v),
        }
    }
}

pub const MAIN: Var<'static> = "main";

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum HigherOrderCStatement<'a> {
    AddrOf {
        lhs: Ident<'a>,
        rhs: Ident<'a>,
    },
    Assign {
        lhs: Ident<'a>,
        rhs: Ident<'a>,
    },
    Load {
        lhs: Ident<'a>,
        rhs: Ident<'a>,
    },
    Store {
        lhs: Ident<'a>,
        rhs: Ident<'a>,
    },
    FunCall {
        lhs: Ident<'a>,
        name: Ident<'a>,
        arg: Ident<'a>,
    },
}

impl Arbitrary for HigherOrderCStatement<'static> {
    fn arbitrary(_g: &mut quickcheck::Gen) -> Self {
        panic!("Don't call this number");
    }
}

impl<'a> Display for HigherOrderCStatement<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::AddrOf { lhs, rhs } => write!(f, "{} <- &{}", lhs, rhs),
            Self::Assign { lhs, rhs } => write!(f, "{} <- {}", lhs, rhs),
            Self::Load { lhs, rhs } => write!(f, "{} <- *{}", lhs, rhs),
            Self::Store { lhs, rhs } => write!(f, "*{} <- {}", lhs, rhs),
            Self::FunCall { lhs, name, arg } => {
                write!(f, "{} <- {}({})", lhs, name, arg)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunDecl<'a> {
    pub name: Var<'a>,
    pub body: Vec<HigherOrderCStatement<'a>>,
}

impl<'a> Display for FunDecl<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        writeln!(f, "fun {0}(p_{0}) {{", self.name)?;
        for stmt in &self.body {
            writeln!(f, "  {}", stmt)?;
        }
        writeln!(f, "  return r_{}", self.name)?;
        writeln!(f, "}}")
    }
}

impl FunDecl<'static> {
    fn gen_with_locals(
        g: &mut quickcheck::Gen,
        locals: &[Var<'static>],
        globals: &[Var<'static>],
        name: Var<'static>,
        num_stmts: usize,
    ) -> Self {
        let mut vars: Vec<_> = globals.iter().copied().map(Ident::Var).collect();
        vars.extend(locals.iter().copied().map(Ident::Var));
        vars.push(Ident::Param(name));
        vars.push(Ident::Return(name));

        let mut body = Vec::with_capacity(num_stmts);
        for _ in 0..num_stmts {
            let lhs = *g.choose(&vars).unwrap();
            let rhs = *g.choose(&vars).unwrap();
            let stmt = match *g.choose(&[0, 1, 2, 3, 4]).unwrap() {
                0 => HigherOrderCStatement::AddrOf { lhs, rhs },
                1 => HigherOrderCStatement::Assign { lhs, rhs },
                2 => HigherOrderCStatement::Load { lhs, rhs },
                3 => HigherOrderCStatement::Store { lhs, rhs },
                4 => HigherOrderCStatement::FunCall {
                    lhs,
                    name: *g.choose(&vars).unwrap(),
                    arg: rhs,
                },
                _ => unreachable!(),
            };
            body.push(stmt);
        }

        Self { name, body }
    }
}

impl Arbitrary for FunDecl<'static> {
    fn arbitrary(_g: &mut quickcheck::Gen) -> Self {
        panic!("Don't call this number");
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let name = self.name;
        Box::new(self.body.shrink().map(|body| Self { name, body }))
    }
}

#[derive(Clone)]
pub struct HigherOrderCProgram<'a> {
    pub funs: Vec<FunDecl<'a>>,
    pub main: FunDecl<'a>,
    pub globals: Vec<Var<'a>>,
}

impl<'a> HigherOrderCProgram<'a> {
    pub fn all_statements(&'a self) -> impl Iterator<Item = HigherOrderCStatement<'a>> {
        self.main
            .body
            .iter()
            .chain(self.funs.iter().flat_map(|f| f.body.iter()))
            .copied()
    }

    pub fn all_statements_with_funs(
        &'a self,
    ) -> impl Iterator<Item = (Var<'a>, HigherOrderCStatement<'a>)> {
        let main_stmts = self.main.body.iter().map(|stmt| (MAIN, *stmt));
        let fun_stmts = self
            .funs
            .iter()
            .flat_map(|f| f.body.iter().map(move |stmt| (f.name, *stmt)));
        main_stmts.chain(fun_stmts)
    }
}

impl Arbitrary for HigherOrderCProgram<'static> {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let num_stmts = g.size();
        let num_funs = num_stmts / 15;
        let num_vars = (num_funs + 2) * 5;
        let num_stmts_per_fun = num_stmts / (num_funs + 1);
        let num_vars_per_fun = num_vars / (num_funs + 2);

        let vars: Vec<_> = get_vars(num_funs + num_vars).collect();
        let globals = &vars[..num_funs + num_vars_per_fun];
        let normal_vars = &vars[num_funs..];
        let main_locals = &normal_vars[num_vars_per_fun..2 * num_vars_per_fun];
        let main = FunDecl::gen_with_locals(g, main_locals, globals, MAIN, num_stmts_per_fun);
        let funs = (0..num_funs)
            .map(|i| {
                let locals = &normal_vars[(i + 2) * num_vars_per_fun..(i + 3) * num_vars_per_fun];
                FunDecl::gen_with_locals(g, locals, globals, globals[i], num_stmts_per_fun)
            })
            .collect();

        Self {
            funs,
            main,
            globals: globals.to_vec(),
        }
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let main = self.main.clone();
        let globals = self.globals.clone();
        let fewer_funs = self.funs.shrink().map(move |funs| Self {
            funs,
            main: main.clone(),
            globals: globals.clone(),
        });
        let funs = self.funs.clone();
        let globals = self.globals.clone();
        let shrunken_main = self.main.shrink().map(move |main| Self {
            funs: funs.clone(),
            main,
            globals: globals.clone(),
        });
        Box::new(fewer_funs.chain(shrunken_main))
    }
}

impl<'a> Display for HigherOrderCProgram<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        writeln!(f, "Globals: {:?}\n", self.globals)?;
        writeln!(f, "{}", self.main)?;
        for fun in &self.funs {
            writeln!(f, "{}", fun)?;
        }
        Ok(())
    }
}

impl<'a> Debug for HigherOrderCProgram<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

fn get_vars(n: usize) -> impl Iterator<Item = Var<'static>> {
    ('a'..='z')
        .map(String::from)
        .chain((1..).map(|n| n.to_string()))
        .map(|s| s.leak() as Var<'static>)
        .take(n)
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Query<'a> {
    PointsTo(Ident<'a>),
    PointedBy(Ident<'a>),
}

impl Arbitrary for Query<'static> {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let num_vars = g.size() / 5 + 2;
        let variables: Vec<_> = get_vars(num_vars).collect();
        let var = g.choose(&variables).unwrap();
        let kind = g.choose(&[0, 1]).unwrap();
        if *kind == 0 {
            Query::PointsTo(Ident::Var(var))
        } else {
            Query::PointedBy(Ident::Var(var))
        }
    }
}

pub mod demand {
    use std::collections::HashSet;

    use super::*;

    crepe::crepe! {
        @input
        struct InPointsToQuery<'a>(Ident<'a>);
        @input
        struct InPointedByQuery<'a>(Ident<'a>);

        @input
        struct AddrOfStatement<'a>(Ident<'a>, Ident<'a>);

        @input
        struct AssignStatement<'a>(Ident<'a>, Ident<'a>);

        @input
        struct LoadStatement<'a>(Ident<'a>, Ident<'a>);

        @input
        struct StoreStatement<'a>(Ident<'a>, Ident<'a>);

        @input
        struct FunDeclStatement<'a>(Var<'a>);

        @input
        struct FunCallStatement<'a>(Ident<'a>, Ident<'a>, Ident<'a>);

        struct Copy<'a>(Ident<'a>, Ident<'a>);

        @output
        #[derive(Debug)]
        pub struct PointsTo<'a>(pub Ident<'a>, pub Ident<'a>);

        @output
        #[derive(Debug)]
        pub struct PointsToQuery<'a>(pub Ident<'a>);
        @output
        #[derive(Debug)]
        pub struct PointedByQuery<'a>(pub Ident<'a>);

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

        // Fun-PT
        PointsTo(Ident::Var(f), Ident::Function(f)) <-
            FunDeclStatement(f),
            PointsToQuery(Ident::Var(f));

        // Fun-PB
        PointsTo(Ident::Var(f), Ident::Function(f)) <-
            FunDeclStatement(f),
            PointedByQuery(Ident::Function(f));

        // Fun-Query-Param
        PointedByQuery(Ident::Function(f)) <-
            FunDeclStatement(f),
            PointsToQuery(Ident::Param(f));

        // Fun-Query-Ret
        PointedByQuery(Ident::Function(f)) <- PointedByQuery(t),
            FunDeclStatement(f),
            PointsTo(Ident::Return(f), t);

        // Arg
        Copy(y, Ident::Param(f)) <- PointsTo(g, f_term),
            let Ident::Function(f) = f_term,
            FunCallStatement(_, g, y);

        // Arg-Query
        PointsToQuery(g) <- PointsTo(y, t), PointedByQuery(t),
            FunCallStatement(_, g, y);

        // Ret
        Copy(Ident::Return(f), x) <- PointsTo(g, f_term),
            let Ident::Function(f) = f_term,
            FunCallStatement(x, g, _);

        // Ret-Query
        PointsToQuery(g) <- PointsToQuery(x),
            FunCallStatement(x, g, _);
    }

    pub fn analyze<'a>(
        program: &'a HigherOrderCProgram<'a>,
        queries: impl IntoIterator<Item = Query<'a>>,
    ) -> (
        HashSet<PointsTo<'a>>,
        HashSet<PointsToQuery<'a>>,
        HashSet<PointedByQuery<'a>>,
    ) {
        let mut runtime = Crepe::new();

        runtime.extend([FunDeclStatement(MAIN)]);
        for fun in &program.funs {
            runtime.extend([FunDeclStatement(fun.name)])
        }
        for statement in program.all_statements() {
            match statement {
                HigherOrderCStatement::AddrOf { lhs, rhs } => {
                    runtime.extend([AddrOfStatement(lhs, rhs)])
                }
                HigherOrderCStatement::Assign { lhs, rhs } => {
                    runtime.extend([AssignStatement(lhs, rhs)])
                }
                HigherOrderCStatement::Load { lhs, rhs } => {
                    runtime.extend([LoadStatement(lhs, rhs)])
                }
                HigherOrderCStatement::Store { lhs, rhs } => {
                    runtime.extend([StoreStatement(lhs, rhs)])
                }
                HigherOrderCStatement::FunCall { lhs, name, arg } => {
                    runtime.extend([FunCallStatement(lhs, name, arg)])
                }
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
        struct AddrOfStatement<'a>(Ident<'a>, Ident<'a>);

        @input
        struct AssignStatement<'a>(Ident<'a>, Ident<'a>);

        @input
        struct LoadStatement<'a>(Ident<'a>, Ident<'a>);

        @input
        struct StoreStatement<'a>(Ident<'a>, Ident<'a>);

        @input
        struct FunDeclStatement<'a>(Var<'a>);

        @input
        struct FunCallStatement<'a>(Ident<'a>, Ident<'a>, Ident<'a>);

        struct Copy<'a>(Ident<'a>, Ident<'a>);

        @output
        #[derive(Debug)]
        pub struct PointsTo<'a>(pub Ident<'a>, pub Ident<'a>);

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

        // Fun
        PointsTo(Ident::Var(x), Ident::Function(x)) <-
            FunDeclStatement(x);

        // Arg
        Copy(y, Ident::Param(f)) <- PointsTo(g, f_term),
            let Ident::Function(f) = f_term,
            FunCallStatement(_, g, y);

        // Ret
        Copy(Ident::Return(f), x) <- PointsTo(g, f_term),
            let Ident::Function(f) = f_term,
            FunCallStatement(x, g, _);
    }

    pub fn analyze<'a>(program: &'a HigherOrderCProgram<'a>) -> HashSet<PointsTo<'a>> {
        let mut runtime = Crepe::new();

        runtime.extend([FunDeclStatement(MAIN)]);
        for fun in &program.funs {
            runtime.extend([FunDeclStatement(fun.name)])
        }
        for statement in program.all_statements() {
            match statement {
                HigherOrderCStatement::AddrOf { lhs, rhs } => {
                    runtime.extend([AddrOfStatement(lhs, rhs)])
                }
                HigherOrderCStatement::Assign { lhs, rhs } => {
                    runtime.extend([AssignStatement(lhs, rhs)])
                }
                HigherOrderCStatement::Load { lhs, rhs } => {
                    runtime.extend([LoadStatement(lhs, rhs)])
                }
                HigherOrderCStatement::Store { lhs, rhs } => {
                    runtime.extend([StoreStatement(lhs, rhs)])
                }
                HigherOrderCStatement::FunCall { lhs, name, arg } => {
                    runtime.extend([FunCallStatement(lhs, name, arg)])
                }
            }
        }

        runtime.run().0
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use quickcheck_macros::quickcheck;

    use super::*;

    #[quickcheck]
    fn demand_driven_correctness(
        prog: HigherOrderCProgram<'static>,
        query: Query<'static>,
    ) -> bool {
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
    fn query_completeness(prog: HigherOrderCProgram<'static>, query: Query<'static>) -> bool {
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
}
