use std::collections::HashSet;
use std::hash::Hash;

use crate::higher_order_c::Ident;

const K: usize = 1;

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Context([usize; K], u8);

impl Context {
    fn select_context(mut self, call_site: usize) -> Self {
        if self.1 as usize == K {
            self.0.copy_within(1.., 0);
        } else {
            self.1 += 1;
        }
        self.0[self.1 as usize - 1] = call_site;
        self
    }

    fn empty() -> Self {
        Self([0; K], 0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct IdentInContext<'a>(Ident<'a>, Context);

impl<'a> Ident<'a> {
    fn in_empty(self) -> IdentInContext<'a> {
        IdentInContext(self, Context::empty())
    }
}

#[derive(Clone, Copy, Debug, Eq)]
struct GlobalsWrapper<'a>(&'a HashSet<Ident<'a>>);

impl<'a> GlobalsWrapper<'a> {
    fn gamma(self, ident: Ident<'a>, c: Context) -> IdentInContext<'a> {
        if self.0.contains(&ident) {
            IdentInContext(ident, Context::empty())
        } else {
            IdentInContext(ident, c)
        }
    }

    fn contains(self, ident: Ident<'a>) -> bool {
        self.0.contains(&ident)
    }
}

impl PartialEq for GlobalsWrapper<'_> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl Hash for GlobalsWrapper<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::ptr::hash(self.0, state)
    }
}

pub mod demand {
    use std::collections::HashSet;

    use crate::higher_order_c::{
        HigherOrderCProgram, HigherOrderCStatement, Ident, Query, Var, MAIN,
    };

    use super::*;

    crepe::crepe! {
        @input
        struct PointsToQuery<'a>(Ident<'a>);
        @input
        struct PointedByQuery<'a>(Ident<'a>);

        @input
        struct AddrOfStatement<'a>(Ident<'a>, Ident<'a>, Var<'a>);

        @input
        struct AssignStatement<'a>(Ident<'a>, Ident<'a>, Var<'a>);

        @input
        struct LoadStatement<'a>(Ident<'a>, Ident<'a>, Var<'a>);

        @input
        struct StoreStatement<'a>(Ident<'a>, Ident<'a>, Var<'a>);

        @input
        struct FunDeclStatement<'a>(Var<'a>);

        @input
        struct FunCallStatement<'a>(Ident<'a>, Ident<'a>, Ident<'a>, Var<'a>, usize);

        // We sneak in a set of global variables as an input to the analysis
        @input
        struct Globals<'a>(GlobalsWrapper<'a>);

        // Variables declared in functions
        @input
        struct VarFun<'a>(Ident<'a>, Var<'a>);

        // // Functions mentioned in other functions (mentioned, containing)
        // @input
        // struct FunFun<'a>(Var<'a>, Var<'a>);

        // // Global variables mentioned in functions
        // @input
        // struct GlobalFun<'a>(Ident<'a>, Var<'a>);

        @input
        struct InInstantiated<'a>(Var<'a>, Context);

        struct Copy<'a>(IdentInContext<'a>, IdentInContext<'a>);

        struct Instantiated<'a>(Var<'a>, Context);

        @output
        #[derive(Debug)]
        pub struct PointsTo<'a>(pub Ident<'a>, pub Ident<'a>);

        @output
        pub struct ContextPointsTo<'a>(pub IdentInContext<'a>, pub IdentInContext<'a>);

        @output
        pub struct ContextPointsToQuery<'a>(pub IdentInContext<'a>);
        @output
        pub struct ContextPointedByQuery<'a>(pub IdentInContext<'a>);

        // Flip
        ContextPointedByQuery(x) <- ContextPointsToQuery(x);
        // Chain
        ContextPointedByQuery(x) <- ContextPointsTo(x, y), ContextPointedByQuery(y);

        // Query-Local-PT
        ContextPointsToQuery(IdentInContext(x, c)) <- Instantiated(f, c), PointsToQuery(x), VarFun(x, f);

        // Query-Local-PB
        ContextPointedByQuery(IdentInContext(x, c)) <- Instantiated(f, c), PointedByQuery(x), VarFun(x, f);

        // Query-Global-PT
        ContextPointsToQuery(x.in_empty()) <- PointsToQuery(x), Globals(gs), (gs.contains(x));

        // Query-Global-PB
        ContextPointedByQuery(x.in_empty()) <- PointedByQuery(x), Globals(gs), (gs.contains(x));

        // Query-Fun
        ContextPointedByQuery(f_term.in_empty()) <- PointedByQuery(f_term), (f_term.is_function());

        // AddrOf-PT
        ContextPointsTo(gs.gamma(x, c), gs.gamma(y, c)) <- Instantiated(f, c),
            AddrOfStatement(x, y, f),
            Globals(gs),
            ContextPointsToQuery(gs.gamma(x, c));

        // AddrOf-PB
        ContextPointsTo(gs.gamma(x, c), gs.gamma(y, c)) <- Instantiated(f, c),
            AddrOfStatement(x, y, f),
            Globals(gs),
            ContextPointedByQuery(gs.gamma(y, c));

        // Assign
        Copy(gs.gamma(y, c), gs.gamma(x, c)) <- Instantiated(f, c),
            AssignStatement(x, y, f),
            Globals(gs);

        // Load
        Copy(z, gs.gamma(x, c)) <- Instantiated(f, c),
            LoadStatement(x, y, f),
            Globals(gs),
            ContextPointsTo(gs.gamma(y, c), z),
            (!z.0.is_function());

        // Load-Query
        ContextPointsToQuery(gs.gamma(y, c)) <- Instantiated(f, c),
            LoadStatement(x, y, f),
            Globals(gs),
            ContextPointsToQuery(gs.gamma(x, c));

        // Store
        Copy(gs.gamma(y, c), z) <- Instantiated(f, c),
            StoreStatement(x, y, f),
            Globals(gs),
            ContextPointsTo(gs.gamma(x, c), z),
            (!z.0.is_function());

        // Store-Query
        ContextPointsToQuery(gs.gamma(x, c)) <- Instantiated(f, c),
            StoreStatement(x, y, f),
            Globals(gs),
            ContextPointsTo(gs.gamma(y, c), t),
            ContextPointedByQuery(t);

        // Fun-PT
        ContextPointsTo(Ident::Var(f).in_empty(), Ident::Function(f).in_empty()) <-
            FunDeclStatement(f),
            ContextPointsToQuery(Ident::Var(f).in_empty());

        // Fun-PB
        ContextPointsTo(Ident::Var(f).in_empty(), Ident::Function(f).in_empty()) <-
            FunDeclStatement(f),
            ContextPointedByQuery(Ident::Function(f).in_empty());

        // Fun-Query-Param
        ContextPointedByQuery(Ident::Function(f).in_empty()) <- Instantiated(f, c),
            FunDeclStatement(f),
            ContextPointsToQuery(IdentInContext(Ident::Param(f), c));

        // Fun-Query-Ret
        ContextPointedByQuery(Ident::Function(f).in_empty()) <- Instantiated(f, c),
            FunDeclStatement(f),
            ContextPointsTo(IdentInContext(Ident::Return(f), c), t),
            ContextPointedByQuery(t);

        // Call
        Instantiated(f, c.select_context(i)) <- Instantiated(g, c),
            FunCallStatement(_, h, _, g, i),
            Globals(gs),
            ContextPointsTo(gs.gamma(h, c), f_term),
            let Ident::Function(f) = f_term.0;

        // Arg
        Copy(gs.gamma(y, c), IdentInContext(Ident::Param(f), c.select_context(i))) <- Instantiated(g, c),
            FunCallStatement(_, h, y, g, i),
            Globals(gs),
            ContextPointsTo(gs.gamma(h, c), f_term),
            let Ident::Function(f) = f_term.0;

        // Ret
        Copy(IdentInContext(Ident::Return(f), c.select_context(i)), gs.gamma(x, c)) <- Instantiated(g, c),
            FunCallStatement(x, h, _, g, i),
            Globals(gs),
            ContextPointsTo(gs.gamma(h, c), f_term),
            let Ident::Function(f) = f_term.0;

        // Arg-Query
        ContextPointsToQuery(gs.gamma(h, c)) <- Instantiated(g, c),
            FunCallStatement(_, h, y, g, _),
            Globals(gs),
            ContextPointsTo(gs.gamma(y, c), t),
            ContextPointedByQuery(t);

        // Ret-Query
        ContextPointsToQuery(gs.gamma(h, c)) <- Instantiated(g, c),
            FunCallStatement(x, h, _, g, _),
            Globals(gs),
            ContextPointsToQuery(gs.gamma(x, c));

        // Copy-PT
        ContextPointsTo(x, t) <- ContextPointsTo(y, t), Copy(y, x),  ContextPointsToQuery(x);

        // Copy-PB
        ContextPointsTo(x, t) <- ContextPointsTo(y, t), Copy(y, x),  ContextPointedByQuery(t);

        // Copy-Query
        ContextPointsToQuery(y) <- Copy(y, x),  ContextPointsToQuery(x);

        // Out
        PointsTo(x.0, y.0) <- ContextPointsTo(x, y);

        // Enter
        // Instantiated(f, Context::empty()) <- FunDeclStatement(f);

        Instantiated(f, c) <- InInstantiated(f, c);

        // Mention-1
        ContextPointedByQuery(Ident::Function(g).in_empty()) <- FunDeclStatement(f),
            FunCallStatement(_, Ident::Var(f), _, g, _),
            ContextPointedByQuery(Ident::Function(f).in_empty());

        // Mention-1
        ContextPointedByQuery(Ident::Function(g).in_empty()) <- FunDeclStatement(f),
            AssignStatement(_, Ident::Var(f), g),
            ContextPointedByQuery(Ident::Function(f).in_empty());

        // Mention-2
        ContextPointedByQuery(Ident::Function(f).in_empty()) <- VarFun(x, f),
            PointsToQuery(x);

        // Mention-3
        ContextPointedByQuery(Ident::Function(f).in_empty()) <- VarFun(x, f),
            PointedByQuery(x);

        // Mention-4
        ContextPointsToQuery(Ident::Function(f).in_empty()) <- //GlobalFun(x, f),
            AssignStatement(x, _, f),
            Globals(gs),
            ContextPointsToQuery(x.in_empty()),
            (gs.contains(x));

        // Mention-4
        ContextPointsToQuery(Ident::Function(f).in_empty()) <- //GlobalFun(x, f),
            AddrOfStatement(x, _, f),
            Globals(gs),
            ContextPointsToQuery(x.in_empty()),
            (gs.contains(x));

        ContextPointsToQuery(Ident::Function(f).in_empty()) <- //GlobalFun(x, f),
            LoadStatement(x, _, f),
            Globals(gs),
            ContextPointsToQuery(x.in_empty()),
            (gs.contains(x));

        ContextPointsToQuery(Ident::Function(f).in_empty()) <- //GlobalFun(x, f),
            FunCallStatement(x, _, _, f, _),
            Globals(gs),
            ContextPointsToQuery(x.in_empty()),
            (gs.contains(x));

        // Mention-5
        ContextPointsToQuery(Ident::Function(f).in_empty()) <- //GlobalFun(x, f),
            StoreStatement(x, _, f),
            Globals(gs),
            ContextPointsToQuery(x.in_empty()),
            (gs.contains(x));

        ContextPointsToQuery(Ident::Function(f).in_empty()) <- //GlobalFun(x, f),
            AddrOfStatement(_, x, f),
            Globals(gs),
            ContextPointedByQuery(x.in_empty()),
            (gs.contains(x));

        ContextPointsToQuery(Ident::Function(f).in_empty()) <- //GlobalFun(x, f),
            AssignStatement(_, x, f),
            Globals(gs),
            ContextPointsTo(x.in_empty(), t),
            ContextPointedByQuery(t),
            (gs.contains(x));

        ContextPointsToQuery(Ident::Function(f).in_empty()) <- //GlobalFun(x, f),
            StoreStatement(_, x, f),
            Globals(gs),
            ContextPointsTo(x.in_empty(), t),
            ContextPointedByQuery(t),
            (gs.contains(x));

        ContextPointsToQuery(Ident::Function(f).in_empty()) <- //GlobalFun(x, f),
            FunCallStatement(_, _, x, f, _),
            Globals(gs),
            ContextPointsTo(x.in_empty(), t),
            ContextPointedByQuery(t),
            (gs.contains(x));

        ContextPointsToQuery(Ident::Function(f).in_empty()) <- //GlobalFun(x, f),
            LoadStatement(_, x, f),
            Globals(gs),
            ContextPointsTo(x.in_empty(), t),
            ContextPointsTo(t, t2),
            ContextPointedByQuery(t2),
            (gs.contains(x));
    }

    pub fn analyze<'a>(
        program: &'a HigherOrderCProgram<'a>,
        queries: impl IntoIterator<Item = Query<'a>>,
    ) -> (
        HashSet<PointsTo<'a>>,
        HashSet<ContextPointsTo<'a>>,
        HashSet<ContextPointsToQuery<'a>>,
        HashSet<ContextPointedByQuery<'a>>,
    ) {
        let mut runtime = Crepe::new();

        let mut functions = HashSet::new();
        let globals = program.globals.iter().map(|&x| Ident::Var(x)).collect();
        let globals = Box::into_raw(Box::new(globals));
        runtime.extend([Globals(GlobalsWrapper(unsafe { &*globals }))]);
        runtime.extend([FunDeclStatement(MAIN)]);
        // Comment out for Approach 1
        runtime.extend([InInstantiated(MAIN, Context::empty())]);
        for fun in &program.funs {
            functions.insert(fun.name);
            runtime.extend([FunDeclStatement(fun.name)])
        }
        for (i, (fun, stmt)) in program.all_statements_with_funs().enumerate() {
            let vars = match stmt {
                HigherOrderCStatement::AddrOf { lhs, rhs } => {
                    runtime.extend([AddrOfStatement(lhs, rhs, fun)]);
                    vec![lhs, rhs]
                }
                HigherOrderCStatement::Assign { lhs, rhs } => {
                    runtime.extend([AssignStatement(lhs, rhs, fun)]);
                    vec![lhs, rhs]
                }
                HigherOrderCStatement::Load { lhs, rhs } => {
                    runtime.extend([LoadStatement(lhs, rhs, fun)]);
                    vec![lhs, rhs]
                }
                HigherOrderCStatement::Store { lhs, rhs } => {
                    runtime.extend([StoreStatement(lhs, rhs, fun)]);
                    vec![lhs, rhs]
                }
                HigherOrderCStatement::FunCall { lhs, name, arg } => {
                    runtime.extend([FunCallStatement(lhs, name, arg, fun, i)]);
                    vec![lhs, name, arg]
                }
            };
            let globals = unsafe { &*globals };
            for var in vars {
                // if functions.contains(&var.name()) {
                //     runtime.extend([FunFun(var.name(), fun)]);
                // }
                if globals.contains(&var) {
                    // runtime.extend([GlobalFun(var, fun)]);
                } else {
                    runtime.extend([VarFun(var, fun)]);
                }
            }
        }

        for query in queries {
            match query {
                Query::PointsTo(x) => runtime.extend([PointsToQuery(x)]),
                Query::PointedBy(x) => runtime.extend([PointedByQuery(x)]),
            }
        }

        let out = runtime.run();
        unsafe {
            drop(Box::from_raw(globals));
        }
        out
    }
}

pub mod exhaustive {
    use std::collections::HashSet;

    use crate::higher_order_c::{HigherOrderCProgram, HigherOrderCStatement, Ident, Var, MAIN};

    use super::*;

    crepe::crepe! {
        @input
        struct AddrOfStatement<'a>(Ident<'a>, Ident<'a>, Var<'a>);

        @input
        struct AssignStatement<'a>(Ident<'a>, Ident<'a>, Var<'a>);

        @input
        struct LoadStatement<'a>(Ident<'a>, Ident<'a>, Var<'a>);

        @input
        struct StoreStatement<'a>(Ident<'a>, Ident<'a>, Var<'a>);

        @input
        struct FunDeclStatement<'a>(Var<'a>);

        @input
        struct FunCallStatement<'a>(Ident<'a>, Ident<'a>, Ident<'a>, Var<'a>, usize);

        // We sneak in a set of global variables as an input to the analysis
        @input
        struct Globals<'a>(GlobalsWrapper<'a>);

        @input
        struct InInstantiated<'a>(Var<'a>, Context);

        struct Copy<'a>(IdentInContext<'a>, IdentInContext<'a>);

        struct Instantiated<'a>(Var<'a>, Context);

        struct ContextPointsTo<'a>(IdentInContext<'a>, IdentInContext<'a>);

        @output
        #[derive(Debug)]
        pub struct PointsTo<'a>(pub Ident<'a>, pub Ident<'a>);

        // AddrOf
        ContextPointsTo(gs.gamma(x, c), gs.gamma(y, c)) <- Instantiated(f, c),
            AddrOfStatement(x, y, f),
            Globals(gs);

        // Assign
        Copy(gs.gamma(y, c), gs.gamma(x, c)) <- Instantiated(f, c),
            AssignStatement(x, y, f),
            Globals(gs);

        // Load
        Copy(z, gs.gamma(x, c)) <- Instantiated(f, c),
            LoadStatement(x, y, f),
            Globals(gs),
            ContextPointsTo(gs.gamma(y, c), z),
            (!z.0.is_function());

        // Store
        Copy(gs.gamma(y, c), z) <- Instantiated(f, c),
            StoreStatement(x, y, f),
            Globals(gs),
            ContextPointsTo(gs.gamma(x, c), z),
            (!z.0.is_function());

        // Fun
        ContextPointsTo(Ident::Var(f).in_empty(), Ident::Function(f).in_empty()) <-
            FunDeclStatement(f);

        // Call
        Instantiated(f, c.select_context(i)) <- Instantiated(g, c),
            FunCallStatement(_, h, _, g, i),
            Globals(gs),
            ContextPointsTo(gs.gamma(h, c), f_term),
            let Ident::Function(f) = f_term.0;

        // Arg
        Copy(gs.gamma(y, c), IdentInContext(Ident::Param(f), c.select_context(i))) <- Instantiated(g, c),
            FunCallStatement(_, h, y, g, i),
            Globals(gs),
            ContextPointsTo(gs.gamma(h, c), f_term),
            let Ident::Function(f) = f_term.0;

        // Ret
        Copy(IdentInContext(Ident::Return(f), c.select_context(i)), gs.gamma(x, c)) <- Instantiated(g, c),
            FunCallStatement(x, h, _, g, i),
            Globals(gs),
            ContextPointsTo(gs.gamma(h, c), f_term),
            let Ident::Function(f) = f_term.0;

        // Copy
        ContextPointsTo(x, t) <- ContextPointsTo(y, t), Copy(y, x);

        // Out
        PointsTo(x.0, y.0) <- ContextPointsTo(x, y);

        // Enter
        // Instantiated(f, Context::empty()) <- FunDeclStatement(f);

        Instantiated(f, c) <- InInstantiated(f, c);
    }

    pub fn analyze<'a>(program: &'a HigherOrderCProgram<'a>) -> HashSet<PointsTo<'a>> {
        let mut runtime = Crepe::new();

        let globals = program.globals.iter().map(|&x| Ident::Var(x)).collect();
        let globals = Box::into_raw(Box::new(globals));
        runtime.extend([Globals(GlobalsWrapper(unsafe { &*globals }))]);
        runtime.extend([FunDeclStatement(MAIN)]);
        // Comment out for Approach 1
        runtime.extend([InInstantiated(MAIN, Context::empty())]);
        for fun in &program.funs {
            runtime.extend([FunDeclStatement(fun.name)])
        }
        for (i, (fun, stmt)) in program.all_statements_with_funs().enumerate() {
            match stmt {
                HigherOrderCStatement::AddrOf { lhs, rhs } => {
                    runtime.extend([AddrOfStatement(lhs, rhs, fun)])
                }
                HigherOrderCStatement::Assign { lhs, rhs } => {
                    runtime.extend([AssignStatement(lhs, rhs, fun)])
                }
                HigherOrderCStatement::Load { lhs, rhs } => {
                    runtime.extend([LoadStatement(lhs, rhs, fun)])
                }
                HigherOrderCStatement::Store { lhs, rhs } => {
                    runtime.extend([StoreStatement(lhs, rhs, fun)])
                }
                HigherOrderCStatement::FunCall { lhs, name, arg } => {
                    runtime.extend([FunCallStatement(lhs, name, arg, fun, i)])
                }
            }
        }

        let (out,) = runtime.run();
        unsafe {
            drop(Box::from_raw(globals));
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use quickcheck_macros::quickcheck;

    use crate::higher_order_c::{HigherOrderCProgram, Query};

    use super::*;

    #[quickcheck]
    fn demand_driven_correctness(
        prog: HigherOrderCProgram<'static>,
        query: Query<'static>,
    ) -> bool {
        let points_to_exhaustive = exhaustive::analyze(&prog);
        let (points_to_demand, ..) = demand::analyze(&prog, [query]);

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
                let res = exhaustive_pointees == demand_pointees;
                if !res {
                    eprintln!(
                        "Exhaustive: {:?}, Demand: {:?}",
                        exhaustive_pointees, demand_pointees
                    );
                }
                res
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
                let res = exhaustive_pointers == demand_pointers;
                if !res {
                    eprintln!(
                        "Exhaustive: {:?}, Demand: {:?}",
                        exhaustive_pointers, demand_pointers
                    );
                }
                res
            }
        }
    }

    #[quickcheck]
    fn context_query_completeness(
        prog: HigherOrderCProgram<'static>,
        query: Query<'static>,
    ) -> bool {
        let (_, points_to, queries_pt, queries_pb) = demand::analyze(&prog, [query]);

        for demand::ContextPointsTo(x, y) in points_to {
            if !queries_pt.contains(&demand::ContextPointsToQuery(x))
                && !queries_pb.contains(&demand::ContextPointedByQuery(y))
            {
                return false;
            }
        }
        true
    }
}
