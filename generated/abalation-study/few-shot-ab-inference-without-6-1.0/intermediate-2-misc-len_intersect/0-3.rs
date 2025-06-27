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
        // Base case: if s1 is empty, then the intersection is also empty.
        assert(s1.intersect(s2).len() == 0);
        assert(s1.intersect(s2).len() <= s1.len());
    } else {
        // Inductive step: assume the property holds for any set smaller than s1.
        let a = s1.choose();
        let s1_minus_a = s1.remove(a);
        
        lemma_len_intersect(s1_minus_a, s2);
        
        if s2.contains(a) {
            assert(s1.intersect(s2).len() == s1_minus_a.intersect(s2).len() + 1);
        } else {
            assert(s1.intersect(s2).len() == s1_minus_a.intersect(s2).len());
        }
        assert(s1.intersect(s2).len() <= s1.len());
    }
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3