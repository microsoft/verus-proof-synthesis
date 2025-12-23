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
        assert(s1.intersect(s2).len() == 0);
    } else {
        let a = s1.choose();
        let s1_prime = s1.remove(a);
        lemma_len_intersect(s1_prime, s2);
        if s2.contains(a) {
            assert(s1.intersect(s2) =~= s1_prime.intersect(s2).insert(a));
            assert(s1.intersect(s2).len() == s1_prime.intersect(s2).len() + 1);
            assert(s1_prime.intersect(s2).len() <= s1_prime.len());
        } else {
            assert(s1.intersect(s2) =~= s1_prime.intersect(s2));
            assert(s1_prime.intersect(s2).len() <= s1_prime.len());
        }
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1