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
    // Base case: if s1 is empty, intersection is also empty
    if s1.len() == 0 {
        assert(s1.intersect(s2).len() == 0);
    } else {
        // Induction step: if s1 is non-empty
        let a = choose |a| s1.contains(a);
        let s1_prime = s1.remove(a);

        // Recursive call
        lemma_len_intersect(s1_prime, s2);

        // Combine results: if a is in both sets, then intersection size decreases by 1
        if s2.contains(a) {
            assert(s1.intersect(s2).len() == s1_prime.intersect(s2).len() + 1);
        } else {
            assert(s1.intersect(s2).len() == s1_prime.intersect(s2).len());
        }

        assert(s1_prime.len() == s1.len() - 1);
    }
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5