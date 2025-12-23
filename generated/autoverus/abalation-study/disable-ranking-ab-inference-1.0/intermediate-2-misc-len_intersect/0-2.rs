
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
    let mut iter = s1.into_iter();
    let mut count_intersect = 0;

    while let Some(element) = iter.next()
        invariant
            s1.finite(),
            count_intersect <= s1.len(),
            s1.intersect(s2).len() <= s1.len(),
            s1.intersect(s2).len() == count_intersect + iter.clone().filter(|x| s2.contains(x)).count(),
            s1.len() == count_intersect + iter.len(),
    {
        if s2.contains(&element) {
            count_intersect += 1;
        }
    }
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2