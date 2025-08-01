
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
    if s1.intersect(s2).is_empty() {
        assert(s1.intersect(s2).len() == 0);
        assert(s1.intersect(s2).len() <= s1.len());
    } else {
        let a = choose|a: A| s1.intersect(s2).contains(a);
        assert(s1.contains(a));
        let s1_minus_a = s1.remove(a);
        lemma_len_intersect::<A>(s1_minus_a, s2);
        assert(s1.intersect(s2).len() == 1 + s1_minus_a.intersect(s2).len());
        assert(s1_minus_a.len() == s1.len() - 1);
        assert(1 + s1_minus_a.intersect(s2).len() <= 1 + s1_minus_a.len());
        assert(1 + s1_minus_a.len() == s1.len());
        assert(1 + s1_minus_a.intersect(s2).len() <= s1.len());
        assert(s1.intersect(s2).len() <= s1.len());
    }
}

} // verus!
// Score: (0, 1)
// Safe: True