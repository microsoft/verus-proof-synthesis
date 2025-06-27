
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
        // Base case: s1 has no elements
        assert(s1.intersect(s2).len() == 0);
    } else {
        // Inductive case: s1 has at least one element
        let elem = choose |x: A| s1.contains(x);
        let s1_rest = s1.remove(elem);

        assert(s1_rest.len() == s1.len() - 1);
        lemma_len_intersect(s1_rest, s2);

        if s2.contains(elem) {
            // If the chosen element is in s2, it's part of the intersection
            assert(s1_rest.intersect(s2).insert(elem) == s1.intersect(s2));
            assert(s1_rest.intersect(s2).len() <== s1.intersect(s2).len() - 1);

            assert(s1.intersect(s2).len() <= s1.len());
        } else {
            // If the chosen element is not in s2, it's not part of the intersection
            assert(s1_rest.intersect(s2) == s1.intersect(s2));
            assert(s1_rest.intersect(s2).len() == s1.intersect(s2).len());

            assert(s1.intersect(s2).len() <= s1.len());
        }
    }
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1