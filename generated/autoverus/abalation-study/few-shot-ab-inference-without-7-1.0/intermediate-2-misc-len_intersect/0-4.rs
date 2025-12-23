
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
    reveal(Set::intersect);

    // Base case when s1 is empty
    assert(s1.len() == 0) by {
        assert(s1.intersect(s2).len() == 0);
    }

    decreases_with_domain {
        old(s1).len() > 0 => {
            let x = s1.choose();
            let s1_minus_x = s1.remove(x);

            // Applying induction hypothesis to the smaller set
            lemma_len_intersect(s1_minus_x, s2);

            if s2.contains(x) {
                assert(s1.intersect(s2) == s1_minus_x.intersect(s2).insert(x));
                assert(s1.intersect(s2).len() == 1 + s1_minus_x.intersect(s2).len());
                assert(1 + s1_minus_x.intersect(s2).len() <= 1 + s1_minus_x.len());
            } else {
                assert(s1.intersect(s2) == s1_minus_x.intersect(s2));
                assert(s1.intersect(s2).len() == s1_minus_x.intersect(s2).len());
            }

            assert(s1.intersect(s2).len() <= s1.len());
        }
    }
}
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1