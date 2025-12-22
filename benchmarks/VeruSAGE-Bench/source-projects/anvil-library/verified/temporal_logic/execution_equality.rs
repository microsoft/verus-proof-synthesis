use vstd::prelude::*;

fn main() {}

verus!{

// File: defs.rs
pub struct Execution<T> {
    pub nat_to_state: spec_fn(nat) -> T,
}


// File: rules.rs
pub proof fn execution_equality<T>(ex1: Execution<T>, ex2: Execution<T>)
    requires forall |i: nat| #[trigger] (ex1.nat_to_state)(i) == (ex2.nat_to_state)(i),
    ensures ex1 == ex2,
{
    assert(ex1.nat_to_state =~= ex2.nat_to_state);
    // fun_ext::<nat, T>(ex1.nat_to_state, ex2.nat_to_state);
}


}
