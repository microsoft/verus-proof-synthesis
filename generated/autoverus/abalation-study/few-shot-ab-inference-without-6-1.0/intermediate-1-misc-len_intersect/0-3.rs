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
        return;
    }

    decreases_by(|s1_prime| s1_prime.len() < s1.len());

    let a = s1.choose();
    let s1_prime = s1.remove(a);

    lemma_len_intersect(s1_prime, s2);

    if s2.contains(a) {
        assert(s1_prime.intersect(s2).len() + 1 == s1.intersect(s2).len());
    } else {
        assert(s1_prime.intersect(s2).len() == s1.intersect(s2).len());
    }
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1