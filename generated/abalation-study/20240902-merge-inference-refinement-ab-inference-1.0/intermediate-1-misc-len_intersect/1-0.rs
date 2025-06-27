
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
    if s1.is_empty() {
        // Base case: if s1 is empty, then s1.intersect(s2) is also empty.
        assert(s1.intersect(s2).is_empty()); 
    } else {
        // Inductive step: assume the lemma holds for all sets smaller than s1.
        let x = s1.choose();
        let rest = s1.remove(x);

        assert(s1.len() == rest.len() + 1);
        
        lemma_len_intersect(rest, s2);
        assert(rest.len() >= s1.intersect(s2).remove(x).len());

        if s2.contains(x) {
            // If x is in s2, then s1.intersect(s2) actually includes x.
            assert(s1.intersect(s2).len() == rest.intersect(s2).len() + 1);
        } else {
            // If x is not in s2, then s1.intersect(s2) does not include x.
            assert(s1.intersect(s2).len() == rest.intersect(s2).len());
        }
    }
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3