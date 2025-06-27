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
    if s1.remove_any().is_some() {
        let a = s1.remove_any().unwrap();
        lemma_len_intersect(s1.remove(a), s2);

        assert(s1.len() + 1 == s1.len() + 1);  // Dummy assert for ensuring decreasing

        if s2.contains(a) {
            assert(s1.intersect(s2).len() + 1 <= s1.len() + 1);
        } else {
            assert(s1.intersect(s2).len() <= s1.len());
        }
    }
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2