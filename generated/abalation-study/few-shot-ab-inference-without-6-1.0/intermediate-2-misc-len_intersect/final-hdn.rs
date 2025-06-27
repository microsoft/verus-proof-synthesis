
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases s1.len(),
{
    if s1.len() == 0 {
    } else {
        let a = s1.choose();
        let s1_rest = s1.remove(a);
        lemma_len_intersect::<A>(s1_rest, s2);
        assert(s1_rest.len() < s1.len());
        if s2.contains(a) {
            assert(s1_rest.intersect(s2).len() <= s1_rest.len());
            assert(s1_rest.len() + 1 == s1.len());
        } else {
            assert(s1_rest.intersect(s2).len() <= s1_rest.len());
            assert(s1_rest.len() == s1.len() - 1);
        }
    }
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1