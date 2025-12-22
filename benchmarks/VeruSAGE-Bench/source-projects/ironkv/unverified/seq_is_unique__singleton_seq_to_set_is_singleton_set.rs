use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn singleton_seq_to_set_is_singleton_set<T>(x: T)
    ensures
        seq![x].to_set() == set![x],
{
}

} // verus!
