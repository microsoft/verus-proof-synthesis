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
    } else {
        let a = s1.choose();
        let s1_minus_a = s1.remove_exactly(a); 

        lemma_len_intersect(s1_minus_a, s2);

        if s2.contains(a) {
            assert(s1.intersect(s2).len() == s1_minus_a.intersect(s2).len() + 1);
        } else {
            assert(s1.intersect(s2).len() == s1_minus_a.intersect(s2).len());
        }
    }
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1