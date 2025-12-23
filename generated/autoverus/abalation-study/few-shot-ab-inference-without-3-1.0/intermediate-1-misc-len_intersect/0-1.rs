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
    decreases_by_lemma!(lemma_len_intersect, s1.len());

    if s1.is_empty() {
        assert(s1.intersect(s2).is_empty()); // Since s1 is empty, their intersection is also empty.
    } else {
        let elem = choose(|elem: A| s1.contains(elem));
        let s1_minus_elem = s1.remove(elem);

        lemma_len_intersect(s1_minus_elem, s2);

        if s2.contains(elem) {
            assert(s1.intersect(s2).len() == s1_minus_elem.intersect(s2).len() + 1);
            assert(s1_minus_elem.intersect(s2).len() < s1.len());
            assert(s1.intersect(s2).len() <= s1.len());
        } else {
            assert(s1.intersect(s2).len() == s1_minus_elem.intersect(s2).len());
            assert(s1_minus_elem.intersect(s2).len() <= s1_minus_elem.len());
            assert(s1_minus_elem.len() < s1.len());
            assert(s1.intersect(s2).len() <= s1.len());
        }
    }
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2