
use vstd::prelude::*;
fn main() {}

verus!{

pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases
        s1.len(),
{
    if !s1.is_empty() {
        let elem = choose |e: A| s1.contains(e);

        assert(s1.without(elem).len() < s1.len());

        lemma_len_intersect::<A>(s1.without(elem), s2);

        assert(s1.intersect(s2).len() <= s1.without(elem).intersect(s2).len() + (
            if s2.contains(elem) { 1 } else { 0 }
        ));
    }
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3