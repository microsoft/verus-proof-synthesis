use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn map_set_finite_auto<A, B>()
    ensures
        forall|s: Set<A>, f: spec_fn(A) -> B| s.finite() ==> #[trigger] (s.map(f).finite()),
{
}

} // verus!
