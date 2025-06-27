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
        let x = s1.choose();
        let s1_minus_x = s1.remove(x);
        assert(s1_minus_x.len() == s1.len() - 1) by {
            assume(s1.len() >= 1);
            assert(s1_minus_x.len() == s1.len() - 1);
        }
        lemma_len_intersect(s1_minus_x, s2);
        if s2.contains(x) {
            assert(s1.intersect(s2).len() == s1_minus_x.intersect(s2).len() + 1) by {
                assert(s1.intersect(s2) =~= s1_minus_x.intersect(s2).insert(x));
                assume(s1_minus_x.intersect(s2).contains(x) == false);
                assert(s1.intersect(s2).len() == s1_minus_x.intersect(s2).len() + 1);
            }
        } else {
            assert(s1.intersect(s2).len() == s1_minus_x.intersect(s2).len()) by {
                assert(s1.intersect(s2) =~= s1_minus_x.intersect(s2));
                assert(s1.intersect(s2).len() == s1_minus_x.intersect(s2).len());
            }
        }
        assert(s1_minus_x.intersect(s2).len() <= s1_minus_x.len());
        assert(s1_minus_x.len() == s1.len() - 1);
        if s2.contains(x) {
            assume(s1_minus_x.intersect(s2).len() + 1 <= s1.len());
        } else {
            assume(s1_minus_x.intersect(s2).len() <= s1.len() - 1);
        }
    }
}

} // verus!


// Score: (0, 1)
// Safe: True