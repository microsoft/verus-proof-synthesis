
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
        // Base case: when the length of s1 is zero, the intersection must also be zero.
        assert(s1.intersect(s2).len() <= s1.len());
    } else {
        // Inductive case: s1 len > 0
        let element = choose |elem: A| s1.contains(elem);

        // Remove one element from s1 to form the smaller set s1'
        let s1_prime = s1.remove(element);

        // Prove the lemma for the smaller set
        lemma_len_intersect(s1_prime, s2);

        // The length of the intersection of s1 and s2 is at most one more than the intersection of s1' and s2
        if s2.contains(element) {
            assert(s1.intersect(s2).len() == s1_prime.intersect(s2).len() + 1);
        } else {
            assert(s1.intersect(s2).len() == s1_prime.intersect(s2).len());
        }

        // Prove the overall property
        assert(s1.intersect(s2).len() <= s1.len());
    }
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5