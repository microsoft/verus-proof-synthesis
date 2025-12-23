
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
    // Base case: If set s1 is empty, the result is immediate.
    if s1.len() == 0 {
        assert(s1.intersect(s2).len() == 0);
        assert(s1.intersect(s2).len() <= s1.len());
        return;
    }

    // General case: Consider removing an arbitrary element x from s1 and prove the invariant holds
    let x = choose|x| s1.contains(x);

    // s1' is s1 with x removed.
    let s1_prime = s1.remove(x);

    // By the decreases clause, we have s1_prime.len() < s1.len()
    lemma_len_intersect(s1_prime, s2); // Inductive hypothesis

    assert(s1_prime.len() < s1.len());
    assert(s1_prime.intersect(s2).len() <= s1_prime.len());

    // Now, analyze s1 intersect s2
    assert(s1.intersect(s2) == if s2.contains(x) {
        s1_prime.intersect(s2).insert(x)
    } else {
        s1_prime.intersect(s2)
    });

    // Depending on whether x is in s2, the size of the intersection can either increase by 1 or stay the same
    if s2.contains(x) {
        assert(s1.intersect(s2).len() == s1_prime.intersect(s2).len() + 1);
        assert(s1_prime.intersect(s2).len() + 1 <= s1_prime.len() + 1);
    } else {
        assert(s1.intersect(s2).len() == s1_prime.intersect(s2).len());
        assert(s1_prime.intersect(s2).len() <= s1_prime.len());
    }

    // Since s1_prime.len() + 1 == s1.len() and s1_prime.len() <= s1.len(), the invariant holds
    assume(s1_prime.len() + 1 == s1.len());
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3