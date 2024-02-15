use crate::simple_c::Query;

mod simple_c;
mod solver;

fn main() {
    let my_program = simple_c! {
        q  <- &x
        w  <- &p
        w  <- &r
        *w <- q
    };
    simple_c::demand::analyze(&my_program, [Query::PointsTo("p")]);
    simple_c::exhaustive::analyze(&my_program);
}
