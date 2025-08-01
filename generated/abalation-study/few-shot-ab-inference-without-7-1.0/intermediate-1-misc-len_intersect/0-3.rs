
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
        // Base case: if s1 is empty, both s1 and s1.intersect(s2) are of length 0.
    } else {
        let a = choose|a| s1.contains(a);
        let s1_minus_a = s1.remove(a);

        assert(s1_minus_a.len() < s1.len());

        lemma_len_intersect(s1_minus_a, s2);

        if s2.contains(a) {
            assert(s1.intersect(s2) == s1_minus_a.intersect(s2).insert(a));
            assert(s1.intersect(s2).len() == s1_minus_a.intersect(s2).len() + 1);
        } else {
            assert(s1.intersect(s2) == s1_minus_a.intersect(s2));
        }
    }
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1