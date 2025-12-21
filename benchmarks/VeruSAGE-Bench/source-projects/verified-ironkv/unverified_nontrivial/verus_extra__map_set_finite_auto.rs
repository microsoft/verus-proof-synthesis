use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::external_body]
pub proof fn map_finite<A, B>(s: Set<A>, f: spec_fn(A) -> B)
    requires
        s.finite(),
    ensures
        s.map(f).finite(),
{
    unimplemented!()
}

pub proof fn map_set_finite_auto<A, B>()
    ensures
        forall|s: Set<A>, f: spec_fn(A) -> B| s.finite() ==> #[trigger] (s.map(f).finite()),
{
}

} // verus!
