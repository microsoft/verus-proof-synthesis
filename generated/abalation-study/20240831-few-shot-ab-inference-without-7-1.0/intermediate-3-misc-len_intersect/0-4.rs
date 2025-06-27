
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
    // Base case: If s1 is empty
    if s1.len() == 0 {
        assert(s1.intersect(s2).len() == 0);
    } else {
        let elem = choose(|e: A| s1.contains(e));
        lemma_len_intersect(s1.remove(elem), s2);
        assert(s1.intersect(s2).len() <= s1.len());
    }
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1