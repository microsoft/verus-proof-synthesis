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
    // Proceed by set induction on s1
    if s1.is_empty() {
        assert(s1.intersect(s2).len() == 0);
        assert(s1.len() == 0);
    } else {
        let x = s1.choose().unwrap();
        let s1_minus_x = s1.remove(x);

        // Apply induction hypothesis
        lemma_len_intersect(s1_minus_x, s2);

        if s2.contains(x) {
            assert(s1.intersect(s2).len() == 1 + s1_minus_x.intersect(s2).len());
        } else {
            assert(s1.intersect(s2).len() == s1_minus_x.intersect(s2).len());
        }

        assert(s1.len() == 1 + s1_minus_x.len());
        assert(s1.intersect(s2).len() <= s1.len());
    }
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1