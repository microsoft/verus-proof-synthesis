
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
    decreases(s1.len());

    if s1.len() == 0 {
        assert(s1.intersect(s2).len() == 0);
    } else {
        let elem = s1.choose();
        let rest = s1.remove(elem);

        lemma_len_intersect(rest, s2);

        if s2.contains(elem) {
            assert(s1.intersect(s2) == rest.intersect(s2).insert(elem));
            assert(s1.intersect(s2).len() == rest.intersect(s2).len() + 1);
        } else {
            assert(s1.intersect(s2) == rest.intersect(s2));
        }
    }
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1