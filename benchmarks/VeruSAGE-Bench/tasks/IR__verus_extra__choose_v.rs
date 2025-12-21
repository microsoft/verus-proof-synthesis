use vstd::prelude::*;
fn main() {}
verus! {

#[doc =
    " Equivalent to `choose |i:int| low <= i < high && p(i)` except it guarantees to pick the smallest"]
#[doc = " such value `i` where `p(i)` is true."]
pub proof fn choose_smallest(low: int, high: int, p: spec_fn(int) -> bool) -> (res: int)
    requires
        exists|i: int| #![trigger(p(i))] low <= i < high && p(i),
    ensures
        low <= res < high,
        p(res),
        forall|i: int| #![trigger(p(i))] low <= i < res ==> !p(i),
{
    proof_from_false() // TODO - replace with correct value
}

} // verus!
