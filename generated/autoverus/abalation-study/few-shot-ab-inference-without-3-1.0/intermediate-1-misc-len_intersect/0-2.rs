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
    reveal(Set::len);

    if s1.len() == 0 {
        assert(s1.intersect(s2).len() == 0);
    } else {
        let elem = choose |e: A| s1.contains(e);

        reveal(Set::intersect);
        if !s2.contains(elem) {
            assert(s1.remove(elem).intersect(s2) == s1.intersect(s2));
        }

        lemma_len_intersect(s1.remove(elem), s2);

        assert(s1.remove(elem).intersect(s2).subset_of(s1.intersect(s2)));
        assert(s1.intersect(s2).len() <= s1.remove(elem).intersect(s2).len() + 1);
    }
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 0