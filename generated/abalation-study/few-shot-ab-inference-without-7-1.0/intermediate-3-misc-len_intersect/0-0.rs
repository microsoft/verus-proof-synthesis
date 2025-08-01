
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
        // Base case: If s1 is empty, then the intersection is also empty
        assert(s1.intersect(s2).len() == 0);
    } else {
        // Inductive case: Remove an arbitrary element from s1 and proceed
        let e = s1.choose();
        let s1_prime = s1.remove(e);
        
        assert(s1_prime.len() < s1.len()); // invariant to ensure s1_prime has strictly smaller length
        
        lemma_len_intersect(s1_prime, s2); // recursive call with smaller set
        
        if s2.contains(e) {
            assert(s1.intersect(s2).len() == s1_prime.intersect(s2).len() + 1);
            assert(s1_prime.intersect(s2).len() <= s1_prime.len());
            assert(s1_prime.len() + 1 <= s1.len());
        } else {
            assert(s1.intersect(s2).len() == s1_prime.intersect(s2).len());
            assert(s1_prime.intersect(s2).len() <= s1_prime.len());
        }
    }
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3