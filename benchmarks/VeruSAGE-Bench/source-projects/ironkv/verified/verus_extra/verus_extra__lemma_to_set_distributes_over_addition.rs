use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

fn main() {}

verus!{

// File: set_lib_ext_v.rs
#[verifier::spinoff_prover]
pub proof fn lemma_to_set_distributes_over_addition<A>(s: Seq<A>, t: Seq<A>)
ensures (s+t).to_set() == s.to_set() + t.to_set()
{
    let left = (s+t).to_set();
    let right = s.to_set() + t.to_set();
    assert forall |x| right.contains(x) implies left.contains(x) by {
        assert(s.to_set()+t.to_set() == s.to_set().union(t.to_set()));
        if s.to_set().contains(x) {
            let si = choose |si| 0<=si<s.len() && s[si] == x;
            assert((s+t)[si] == x);
        } else {
            let ti = choose |ti| 0<=ti<t.len() && t[ti] == x;
            assert((s+t)[s.len() + ti] == x);
        }
    }
    assert_sets_equal!(left, right);
}


}
