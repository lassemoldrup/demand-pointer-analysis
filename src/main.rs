use crate::simple_java::Query;

mod simple_c;
mod simple_java;
mod solver;

fn main() {
    let my_program = simple_java! {
        o   <- new
        a   <- new
        o.f <- a
        x   <- o.f
        p   <- o
    };
    let demand_res = simple_java::demand::analyze(&my_program, [Query::PointsTo("x")]);
    println!("{demand_res:?}");
    let exhaustive_res = simple_java::exhaustive::analyze(&my_program);
    println!("{exhaustive_res:?}");
}
