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
    decreases_when(s1.len() > 0);
    if s1.len() == 0 {
        // Base case: If s1 is empty, its intersection with any set is also empty,
        // so the lemma's conclusion holds trivially.
        assert(s1.intersect(s2).len() <= s1.len());
    } else {
        // Induction step: Remove an arbitrary element from s1 and apply the
        // induction hypothesis to the resulting set.
        let e = s1.choose(); // Choose an arbitrary element from s1.
        let s1_without_e = s1.remove(e); // Remove the chosen element from s1.
        lemma_len_intersect(s1_without_e, s2); // Apply the induction hypothesis.
        assert(s1_without_e.len() == s1.len() - 1);
        assert(s1.intersect(s2).len() <= s1_without_e.intersect(s2).len() + 1);
        assert(s1_without_e.intersect(s2).len() + 1 <= s1.len()); // Use the induction hypothesis.
        assert(s1.intersect(s2).len() <= s1.len());
    }
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1