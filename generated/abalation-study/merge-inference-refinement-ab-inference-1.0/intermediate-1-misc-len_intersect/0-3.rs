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
        // If s1 is empty, the intersection is also empty, and the property holds trivially.
    } else {
        // Choose an arbitrary element from the set s1.
        let elem = choose |e: A| s1.contains(e);
        // Prove that the set without this element is smaller.
        lemma_len_intersect(s1.remove(elem), s2);
        // If elem is in the intersection, removing it from s1 decreases both lengths.
        // If elem is not in the intersection, removing it from s1 doesn't affect the intersection length.
        assert(s1.intersect(s2).len() <= s1.len());
    }
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3