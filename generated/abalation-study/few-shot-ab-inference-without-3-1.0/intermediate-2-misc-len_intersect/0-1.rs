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
        // intersection of empty set with any set is empty, hence the length is zero
    } else {
        let elem = choose |x| s1.contains(x);
        let s1_without_elem = s1.remove(elem);

        lemma_len_intersect::<A>(s1_without_elem, s2);

        assert(s1.intersect(s2) == if s2.contains(elem) { set_with(elem).union(s1_without_elem.intersect(s2)) } else { s1_without_elem.intersect(s2) });
        assert(s1_without_elem.len() + 1 == s1.len());

        if s2.contains(elem) {
            assert(s1.intersect(s2).len() == s1_without_elem.intersect(s2).len() + 1);
            assert(s1_without_elem.intersect(s2).len() <= s1_without_elem.len());
            assert(s1.intersect(s2).len() <= s1_without_elem.len() + 1);
        } else {
            assert(s1.intersect(s2).len() == s1_without_elem.intersect(s2).len());
            assert(s1_without_elem.intersect(s2).len() <= s1_without_elem.len());
        }
    }
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1