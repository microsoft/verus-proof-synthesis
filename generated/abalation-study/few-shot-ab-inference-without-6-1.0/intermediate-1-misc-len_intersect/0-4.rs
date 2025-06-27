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
        // Base case: if the length of `s1` is zero, the intersect set will also be empty.
    } else {
        // Inductive case: we assume the property holds for any subset of `s1` with size less than `s1.len()`.
        let x = s1.choose(); // Choose an arbitrary element from `s1`.

        // Split `s1` into `x` and the rest `s1_` (i.e., `s1_` does not contain `x`).
        let s1_ = s1.remove(x);
        assert(s1_.len() == s1.len() - 1);

        lemma_len_intersect(s1_, s2); // Apply the inductive hypothesis.

        // If `x` is in `s2`, add it back to the intersection of `s1_` and `s2`.
        // It means `x` contributes to the length of the intersection.
        if s2.contains(x) {
            assert(s1.intersect(s2).len() == s1_.intersect(s2).len() + 1);
        } else {
            assert(s1.intersect(s2).len() == s1_.intersect(s2).len());
        }
    }
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3