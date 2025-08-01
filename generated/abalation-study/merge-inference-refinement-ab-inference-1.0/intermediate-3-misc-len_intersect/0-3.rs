
use vstd::prelude::*;
fn main() {}

verus! {
      
pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases
        s1.len(),
{
    decreases_when(s1.len() > 0); // Ensures that the size of s1 decreases in recursive calls

    if s1.is_empty() {
        // Base case: If s1 is empty, the intersection is also empty, and the length is 0
        assert(s1.len() == 0);
        assert(s1.intersect(s2).len() == 0);
    } else {
        // Recursive case: Remove an arbitrary element from s1 and prove the property for the remainder
        let a = s1.choose(); // Choose an arbitrary element from s1
        let remainder = s1.remove(a);

        lemma_len_intersect(remainder, s2);

        if s2.contains(a) {
            // If s2 contains the chosen element, the intersection length increases by 1
            assert(s1.intersect(s2).len() == remainder.intersect(s2).len() + 1);
        } else {
            // If s2 does not contain the chosen element, the intersection length does not change
            assert(s1.intersect(s2).len() == remainder.intersect(s2).len());
        }
    }
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1