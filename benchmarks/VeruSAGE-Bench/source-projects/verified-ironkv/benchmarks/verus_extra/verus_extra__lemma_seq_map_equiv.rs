use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

fn main() {}

verus!{

// File: set_lib_ext_v.rs
pub proof fn lemma_seq_map_equiv<A, B>(f: spec_fn(A) -> B, g: spec_fn(int, A) -> B)
requires
    forall |i: int, a: A| #[trigger] g(i, a) == f(a)
ensures
    forall |s: Seq<A>| s.map_values(f) == s.map(g)
{
    assert forall |s: Seq<A>| s.map_values(f) == s.map(g) by {
        assert_seqs_equal!(s.map_values(f), s.map(g));
    }
}


}
