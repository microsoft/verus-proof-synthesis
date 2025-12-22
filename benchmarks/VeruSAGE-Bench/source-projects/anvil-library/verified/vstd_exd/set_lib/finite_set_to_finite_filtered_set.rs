use vstd::prelude::*;

fn main() {}

verus! {

pub proof fn finite_set_to_finite_filtered_set<A>(s: Set<A>, f: spec_fn(A) -> bool)
    requires s.finite(),
    ensures s.filter(f).finite(),
    decreases s.len()
{
    if s.len() != 0 {
        let x = s.choose();
        finite_set_to_finite_filtered_set(s.remove(x), f);
    }
}

}
