use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

fn main() {}

verus!{

// File: set_lib_ext_v.rs
pub proof fn seq_map_values_concat<A, B>(s1: Seq<A>, s2: Seq<A>, f: spec_fn(A) -> B)
    ensures (s1 + s2).map_values(f) == s1.map_values(f) + s2.map_values(f)
{
    assert_seqs_equal!((s1 + s2).map_values(f) == s1.map_values(f) + s2.map_values(f), i => {
        if i < s1.len() {
            assert((s1+s2)[i] == s1[i]);
        } else {
            assert((s1+s2)[i] == s2[i - s1.len()]);
        }
    });
}


}
