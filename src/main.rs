use crate::simple_c::Query;

mod simple_c;
mod solver;

fn main() {
    use simple_c::SimpleCStatement as S;
    let my_program = [
        S::AddrOf { lhs: "q", rhs: "x" },
        S::AddrOf { lhs: "w", rhs: "p" },
        S::AddrOf { lhs: "w", rhs: "r" },
        S::Store { lhs: "w", rhs: "q" },
    ];
    simple_c::demand::analyze(my_program.into(), [Query::PointsTo("p")]);
}
