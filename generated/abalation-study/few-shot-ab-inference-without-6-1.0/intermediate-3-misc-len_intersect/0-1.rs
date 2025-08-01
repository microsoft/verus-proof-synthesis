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
    if !s1.is_empty() {
        let elem = s1.choose();
        assert(s1.remove(elem).finite());

        lemma_len_intersect(s1.remove(elem), s2);

        if s2.contains(elem) {
            assert(s1.intersect(s2).len() == s1.remove(elem).intersect(s2).len() + 1);
            assert(s1.intersect(s2).len() + 1 <= s1.len());
        } else {
            assert(s1.intersect(s2).len() == s1.remove(elem).intersect(s2).len());
            assert(s1.len() == s1.remove(elem).len() + 1);
        }
    }
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4