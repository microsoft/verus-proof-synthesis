
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
    // Base case: If s1 is empty, the intersection is also empty.
    if s1.len() == 0 {
        assert(s1.intersect(s2).len() == 0);
    } else {
        let a = s1.choose();
        let s1_prime = s1.remove(a);

        // Inductive step: Assume the lemma holds for s1', prove it for s1
        lemma_len_intersect(s1_prime, s2);

        if s2.contains(a) {
            assert(s1.intersect(s2).len() == s1_prime.intersect(s2).len() + 1);
            assert(s1.intersect(s2).len() <= s1_prime.len() + 1);
            assert(s1_prime.len() < s1.len());
            assert(s1_prime.len() + 1 == s1.len());
        } else {
            assert_s1_intersect_s2_same_as_s1_prime(s1_prime, s2, a); // A helper lemma
        }

        assert(s1.intersect(s2).len() <= s1.len());
    }
}

proof fn assert_s1_intersect_s2_same_as_s1_prime<A>(s1_prime: Set<A>, s2: Set<A>, a: A)
    requires
        !s2.contains(a),
        s1_prime.intersect(s2) == s1_prime.intersect(s2),
    ensures
        s1_prime.insert(a).intersect(s2).len() == s1_prime.intersect(s2).len(),
{
    // If 'a' is not in s2, then adding 'a' to s1' will not change the intersection.
    assert(s1_prime.insert(a).intersect(s2) == s1_prime.intersect(s2));
}
}

// Score: (1, 2)
// Safe: True