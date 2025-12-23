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
    } else {
        let a = choose|a: A| s1.contains(a);
        let rest = s1.remove(a);
        lemma_len_intersect::<A>(rest, s2);
        if s2.contains(a) {
        } else {
        }
    }
}

} // verus!



// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2