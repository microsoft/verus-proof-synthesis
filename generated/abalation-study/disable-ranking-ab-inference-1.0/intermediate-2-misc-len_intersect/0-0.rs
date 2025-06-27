
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
        assert(s1.intersect(s2).len() == 0);
    } else {
        let a = choose |a: A| s1.contains(a);
        assert(s1.remove(a).len() < s1.len()); // By finiteness of s1
        
        lemma_len_intersect(s1.remove(a), s2);
        
        if s2.contains(a) {
            assert(s1.intersect(s2).union(set![a]) == s1.intersect(s2).add(a));
            assert(s1.intersect(s2).add(a).len() == s1.intersect(s2).len() + 1);
            assert(s1.intersect(s2).len() + 1 <= s1.len());
        } else {
            assert(s1.intersect(s2).len() == s1.intersect(s2));
        }
    }
}

}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2