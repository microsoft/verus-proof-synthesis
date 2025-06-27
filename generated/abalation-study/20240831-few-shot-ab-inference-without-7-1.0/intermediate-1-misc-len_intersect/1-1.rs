
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
    decreases(s1.len());

    if s1.is_empty() {
        // Base case: If s1 is empty, the intersection is also empty
        assert(s1.intersect(s2).is_empty());
    } else {
        let a = s1.choose();
        let rest = s1.remove(a);
        lemma_len_intersect(rest, s2);
        if s2.contains(a) {
            assert(rest.intersect(s2).len() <= rest.len());
            assert(rest.intersect(s2).insert(a).len() <= rest.len() + 1);
            assert(s1.intersect(s2).len() == rest.intersect(s2).insert(a).len());
            assert(rest.len() + 1 == s1.len());
        } else {
            assert(rest.intersect(s2).len() == s1.intersect(s2).len());
            assert(rest.len() == s1.len() - 1);
        }
    }
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1