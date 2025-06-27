
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
        // Base case: An empty set intersected with any set is still empty.
    } else {
        let x = choose|x: A| s1.contains(x);
        // We reduce to a smaller problem by removing 'x' from 's1'.
        assert(s1.remove(x).len() < s1.len());
        lemma_len_intersect(s1.remove(x), s2);
        if s2.contains(x) {
            assert(s1.intersect(s2).len() == s1.remove(x).intersect(s2).len() + 1);
        } else {
            assert(s1.intersect(s2).len() == s1.remove(x).intersect(s2).len());
        }
    }
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4