
use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases s1.len(),
{
    if s1.is_empty() {
        assert(s1.intersect(s2).is_empty());
        assert(s1.intersect(s2).len() == 0);
        assert(s1.len() == 0);
    } else {
        let e = choose|e: A| s1.contains(e);
        assert(s1.contains(e));
        let s1_rest = s1.remove(e);
        lemma_len_intersect(s1_rest, s2);
        if s1_rest.intersect(s2).contains(e) {
            assert(s1_rest.intersect(s2).insert(e) == s1.intersect(s2));
            assert(s1_rest.intersect(s2).len() + 1 == s1.intersect(s2).len());
        } else {
            assert(s1_rest.intersect(s2) == s1.intersect(s2));
            assert(s1_rest.intersect(s2).len() == s1.intersect(s2).len());
        }
        assert(s1_rest.len() + 1 == s1.len());
        assert(s1.intersect(s2).len() <= s1.len());
    }
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1