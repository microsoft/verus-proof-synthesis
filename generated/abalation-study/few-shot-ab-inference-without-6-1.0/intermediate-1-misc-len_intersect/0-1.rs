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
    if s1.len() == 0 {
    } else {
        let a = choose |a| s1.contains(a);
        lemma_len_intersect(s1.remove(a), s2);
        assert(s1.len() == s1.remove(a).len() + 1);
        assert(s1.intersect(s2).len() <= s1.remove(a).intersect(s2).len() + if s2.contains(a) { 1 } else { 0 });
    }
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1