
use vstd::prelude::*;
fn main() {}

verus! {
    
pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases
        s1.len(),
{
    if s1.is_empty() {
        assert(s1.intersect(s2).is_empty());
        assert(s1.intersect(s2).len() == 0);
    } else {
        let a = choose |a| s1.contains(a);
        assert(s1.remove(a).len() < s1.len());
        lemma_len_intersect(s1.remove(a), s2);

        if s2.contains(a) {
            assert(s1.intersect(s2).insert(a) == s1.remove(a).intersect(s2).insert(a));
            assert(s1.intersect(s2).insert(a).len() == 1 + s1.remove(a).intersect(s2).len());
            assert(1 + s1.remove(a).intersect(s2).len() <= 1 + s1.remove(a).len());
            assert(1 + s1.remove(a).len() == s1.len());
        } else {
            assert(s1.intersect(s2) == s1.remove(a).intersect(s2));
            assert(s1.intersect(s2).len() == s1.remove(a).intersect(s2).len());
            assert(s1.remove(a).intersect(s2).len() <= s1.remove(a).len());
            assert(s1.remove(a).len() == s1.len() - 1);
        }
    }
}
}

// Score: (1, 0)
// Safe: True