
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
        assert(s1.intersect(s2).is_empty());
    } else {
        let x = choose(|x| s1.contains(x));
        lemma_len_intersect::<A>(s1.remove(x), s2);

        if s2.contains(x) {
            assert(s1.intersect(s2).len() == s1.remove(x).intersect(s2).len() + 1);
        } else {
            assert(s1.intersect(s2).len() == s1.remove(x).intersect(s2).len());
        }
    }
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1