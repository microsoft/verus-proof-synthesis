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
    let mut i: int = 0;

    while i < n
        invariant
            0 <= i <= n,
            s1.len() == n,
            s1.finite(),
            s1.intersect(s2).len() <= n,
    {
        i = i + 1;
    }
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1