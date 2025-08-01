
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
    if s1.len() == 0 {
        // Base case: when s1 is empty, s1.intersect(s2) is also empty
        assert(s1.intersect(s2).len() == 0);
    } else {
        let el = choose |el: A| s1.contains(el);
        assert(s1.remove(el).len() == s1.len() - 1);
        lemma_len_intersect::<A>(s1.remove(el), s2);
        
        if s2.contains(el) {
            assert(s1.intersect(s2).len() + 1 == s1.remove(el).intersect(s2).len());
        } else {
            assert(s1.intersect(s2).len() == s1.remove(el).intersect(s2).len());
        }
    }
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4