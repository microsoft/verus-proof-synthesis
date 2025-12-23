
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
        // Base case: if the length of s1 is 0, the result is trivial
        assert(s1.intersect(s2).len() == 0);
    } else {
        // Recursive case: pick an arbitrary element from s1
        let a = choose |a| s1.contains(a);
        assert(s1.remove(a).len() == s1.len() - 1);
        
        lemma_len_intersect::<A>(s1.remove(a), s2);
        
        if s2.contains(a) {
            assert(s1.intersect(s2).insert(a) == s1.intersect(s2).union(set![a]));
            assert(s1.remove(a).intersect(s2).insert(a).len() == s1.intersect(s2).len());
            assert(s1.intersect(s2).len() == s1.remove(a).intersect(s2).len() + 1);
            assert(s1.intersect(s2).len() <= s1.len());
        } else {
            assert(s1.intersect(s2).len() == s1.remove(a).intersect(s2).len());
            assert(s1.intersect(s2).len() <= s1.len());
        }
    }
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4