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
    } else {
        let x = s1.choose();
        let s1_ = s1.remove(x);
        assert(s1_.len() == s1.len() - 1);
        lemma_len_intersect(s1_, s2);
        if s2.contains(x) {
            assert(s1.intersect(s2).len() == s1_.intersect(s2).len() + 1);
        } else {
            assert(s1.intersect(s2).len() == s1_.intersect(s2).len());
        }
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3