use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

fn main() {}

verus!{

// File: set_lib_ext_v.rs
#[verifier::spinoff_prover]
pub proof fn lemma_seq_push_to_set<A>(s: Seq<A>, x: A)
    ensures s.push(x).to_set() == s.to_set().insert(x)
{
    assert_sets_equal!(s.push(x).to_set() == s.to_set().insert(x), elem => {
        if elem == x {
            assert(s.push(x)[s.len() as int] == x);
            assert(s.push(x).contains(x))
        } else {
            if s.to_set().insert(x).contains(elem) {
                assert(s.to_set().contains(elem));
                let i = choose |i: int| 0 <= i < s.len() && s[i] == elem;
                assert(s.push(x)[i] == elem);
            }
        }
    });
}


}
