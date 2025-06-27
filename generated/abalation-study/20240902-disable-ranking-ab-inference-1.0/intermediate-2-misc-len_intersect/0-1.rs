
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
    decreases_by {
        if s1.len() == 0 {
            return;
        }

        let e = choose |e: A| s1.contains(e);
        let s1_new = s1.remove(e);

        assert(s1_new.len() < s1.len());
        assert(s1_new.union(Set::singleton(e)).len() == s1.len());
        assert(s1_new.intersect(s2).union(Set::singleton(e)).len() <= s1.len());
        lemma_len_intersect(s1_new, s2);
    }
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1