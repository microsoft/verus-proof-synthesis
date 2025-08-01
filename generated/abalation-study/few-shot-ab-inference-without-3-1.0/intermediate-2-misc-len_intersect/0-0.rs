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
    let n = s1.len();

    // Base case: If the set is empty, the property holds trivially
    if n == 0 {
        assert(s1.intersect(s2).len() <= s1.len());
        return;
    }

    // Inductive step:
    let x = s1.choose();
    let s1_minus_x = s1.remove(x);

    lemma_len_intersect(s1_minus_x, s2);

    if s2.contains(x) {
        assert(s1.intersect(s2).len() == s1_minus_x.intersect(s2).len() + 1);
        assert(s1_minus_x.intersect(s2).len() <= s1_minus_x.len());
        assert(s1.intersect(s2).len() <= s1.len());
    } else {
        assert(s1.intersect(s2).len() == s1_minus_x.intersect(s2).len());
        assert(s1_minus_x.intersect(s2).len() <= s1_minus_x.len());
        assert(s1.intersect(s2).len() <= s1.len());
    }
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3