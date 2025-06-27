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
        assert(s1.intersect(s2).len() == 0);
    } else {
        let a = s1.choose();
        let s1_rest = s1.remove(a);
        lemma_len_intersect(s1_rest, s2);
        assert(s1.len() == s1_rest.len() + 1);
        if s2.contains(a) {
            assert(s1.intersect(s2).len() == s1_rest.intersect(s2).len() + 1);
        } else {
            assert(s1.intersect(s2).len() == s1_rest.intersect(s2).len());
        }
    }
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3