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
    decreases_by(check_lemma_len_intersect);

    if s1.len() == 0 {
        assert(s1.intersect(s2).len() == 0);
    } else {
        let a = s1.choose();
        let rest = s1.remove(a);
        lemma_len_intersect::<A>(rest, s2);
        if s2.contains(a) {
            assert(rest.intersect(s2).insert(a) =~= s1.intersect(s2));
        } else {
            assert(rest.intersect(s2) =~= s1.intersect(s2));
        }
    }
}

pub proof fn check_lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    decreases
        s1.len(),
{
    if s1.len() == 0 {
        // Base case is trivially true
    } else {
        let a = s1.choose();
        let rest = s1.remove(a);
        assert(rest.len() < s1.len()); // Decrease measure to ensure termination
        check_lemma_len_intersect(rest, s2);
    }
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1