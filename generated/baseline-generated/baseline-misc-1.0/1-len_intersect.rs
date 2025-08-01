
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
        // Base case: When s1 is empty
        assert(s1.intersect(s2).len() == 0);
    } else {
        // Inductive step: We assume the statement holds for all sets smaller than s1

        // Let's take an element x from s1 and define a new set s1' without x
        let x = s1.choose();
        let s1_prime = s1.remove(x);

        // Use the induction hypothesis
        lemma_len_intersect(s1_prime, s2);

        // We have s1 = s1' ∪ {x}, and considering intersection:
        if s2.contains(x) {
            // Case: x is in s2
            // s1 ∩ s2 = (s1' ∩ s2) ∪ {x}
            assert(s1.intersect(s2) == s1_prime.intersect(s2).insert(x));
            
            // Applying the induction hypothesis
            assert(s1_prime.intersect(s2).len() <= s1_prime.len());
            assert(s1.intersect(s2).len() == s1_prime.intersect(s2).len() + 1);

            // Hence, s1 ∩ s2’s length is at most s1’s length
            assert(s1_prime.len() + 1 == s1.len());
            assert(s1.intersect(s2).len() <= s1.len());
        } else {
            // Case: x is not in s2
            // s1 ∩ s2 = s1' ∩ s2
            assert(s1.intersect(s2) == s1_prime.intersect(s2));
            assert(s1.intersect(s2).len() == s1_prime.intersect(s2).len());

            // Applying the induction hypothesis
            assert(s1_prime.intersect(s2).len() <= s1_prime.len());
            assert(s1.len() == s1_prime.len() + 1);

            // Hence, s1 ∩ s2’s length is at most s1’s length
            assert(s1.intersect(s2).len() <= s1.len());
        }
    }
}
}

// Score: (0, 1)
// Safe: True