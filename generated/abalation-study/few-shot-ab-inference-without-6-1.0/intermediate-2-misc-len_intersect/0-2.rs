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
        assert!(s1.intersect(s2).len() == ( 0 ) as nat);
    } else {
        let x = s1.choose();
        let s1_minus_x = s1.remove(x);
        
        lemma_len_intersect::<A>(s1_minus_x, s2);
        
        if s2.contains(x) {
            assert!(s1.intersect(s2).len() == s1_minus_x.intersect(s2).len() + ( 1 ) as nat);
        } else {
            assert!(s1.intersect(s2).len() == s1_minus_x.intersect(s2).len());
        }
    }
}
}


// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2