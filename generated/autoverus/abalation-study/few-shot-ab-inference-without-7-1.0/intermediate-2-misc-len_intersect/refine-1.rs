
use vstd::prelude::*;
fn main() {}
verus! {

pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases s1.len(),
{
    if s1.len() == 0 {
        assert(s1.intersect(s2).len() == 0);
    } else {
        let a = s1.choose();
        let s1_less_a = s1.remove(a);
        lemma_len_intersect(s1_less_a, s2);
        if s2.contains(a) {
            assert(s1.intersect(s2).len() == s1_less_a.intersect(s2).len() + 1);
        } else {
            assert(s1.intersect(s2).len() == s1_less_a.intersect(s2).len());
        }
        // Loop invariant added here
        assert(s1.finite());
        assert(s1_less_a.len() == s1.len() - 1);
    }
}

} // verus!
