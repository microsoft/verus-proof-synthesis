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
        assert(s1.intersect(s2).len() == 0);
    } else {
        let elt = choose|e: A| s1.contains(e);
        assert(s1.remove(elt).len() == s1.len() - 1);
        lemma_len_intersect::<A>(s1.remove(elt), s2);
        if s2.contains(elt) {
            assert(s1.intersect(s2).insert(elt) == s1.remove(elt).intersect(s2).insert(elt));
            assert(s1.intersect(s2).len() == s1.remove(elt).intersect(s2).len() + 1);
        } else {
            assert(s1.intersect(s2) == s1.remove(elt).intersect(s2));
        }
    }
}

} // verus!

// Score: (0, 3)
// Safe: True