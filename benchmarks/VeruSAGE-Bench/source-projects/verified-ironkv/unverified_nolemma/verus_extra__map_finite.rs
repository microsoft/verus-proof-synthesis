use vstd::prelude::*;
fn main() {}
verus! {

pub open spec fn set_fold<A, B>(s: Set<A>, zero: B, f: spec_fn(B, A) -> B) -> B
    recommends
        s.finite(),
    decreases s.len(),
{
    if s.finite() {
        if s.len() == 0 {
            zero
        } else {
            let a = s.choose();
            f(set_fold(s.remove(a), zero, f), a)
        }
    } else {
        zero
    }
}

spec fn map_fold<A, B>(s: Set<A>, f: spec_fn(A) -> B) -> Set<B>
    recommends
        s.finite(),
{
    set_fold(s, Set::empty(), |s1: Set<B>, a: A| s1.insert(f(a)))
}

pub proof fn map_finite<A, B>(s: Set<A>, f: spec_fn(A) -> B)
    requires
        s.finite(),
    ensures
        s.map(f).finite(),
{
}

} // verus!
