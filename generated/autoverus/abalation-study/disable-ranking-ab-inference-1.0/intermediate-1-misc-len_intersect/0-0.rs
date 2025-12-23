//an example from Verus tutorial. VERY difficult.

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
        // Base case: if s1 is empty, then s1.intersect(s2) is also empty
        // By definition, len of empty set is 0, and 0 <= 0 holds.
    } else {
        // Inductive case: Consider an element `a` in `s1`
        let a = s1.choose();
        let s1_minus_a = s1.remove(a);
        
        // s1's finite implies s1_minus_a is also finite
        assert(s1_minus_a.finite());
        
        // Apply the induction hypothesis to s1_minus_a
        lemma_len_intersect::<A>(s1_minus_a, s2);
        
        // Prove the inductive step
        if s2.contains(a) {
            assert(s1_minus_a.intersect(s2).insert(a) == s1.intersect(s2));
        } else {
            assert(s1_minus_a.intersect(s2) == s1.intersect(s2));
        }
        assert(s1_minus_a.intersect(s2).len() <= s1_minus_a.len());
        assert(s1.intersect(s2).len() <= s1.len());
    }
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1