
use vstd::prelude::*;
fn main() {}

verus!

pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases
        s1.len(), // Decreases the size of the first set to ensure termination and completeness of the proof
{
    // We need to prove that the length of the intersection of s1 and s2 is less than or equal to the length of s1
    assert(s1.intersect(s2).finite());

    // If s1 is empty, then s1.intersect(s2) is also empty, so the result is trivially true
    if s1.len() == 0 {
        assert(s1.intersect(s2).len() == 0);
    } else {
        // Let's break the set s1 into s1_head (an arbitrary element) and s1_tail (all other elements)
        let s1_head = choose |x: A| s1.contains(x);
        let s1_tail = s1.remove(s1_head);

        // We need a proof that s1_head is indeed part of s1
        assert(s1.contains(s1_head));

        // Apply induction to the smaller set s1_tail
        lemma_len_intersect::<A>(s1_tail, s2);

        // Now, let's reason about the length of the intersection
        if s2.contains(s1_head) {
            // If s2 contains s1_head, then the length of the intersection increases by 1
            assert(s1_tail.intersect(s2).len() + 1 == s1.intersect(s2).len());
        } else {
            // If s2 doesn't contain s1_head, then the length of the intersection remains the same
            assert(s1_tail.intersect(s2).len() == s1.intersect(s2).len());
        }

        // We conclude by combining the results
        assert(s1_tail.intersect(s2).len() <= s1_tail.len());
        assert(s1_tail.len() + 1 == s1.len());
        if s2.contains(s1_head) {
            assert(s1.intersect(s2).len() == s1_tail.intersect(s2).len() + 1);
            assert(s1_tail.intersect(s2).len() + 1 <= s1_tail.len() + 1);
            assert(s1.intersect(s2).len() <= s1.len());
        } else {
            assert(s1.intersect(s2).len() == s1_tail.intersect(s2).len());
            assert(s1.intersect(s2).len() <= s1.tail.len());
        }
    }
}
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1