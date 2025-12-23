use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;

fn main() {}

verus!{

// File: set_lib_ext_v.rs
pub proof fn set_map_union<A, B>(s1: Set<A>, s2: Set<A>, f: spec_fn(A) -> B)
    ensures (s1 + s2).map(f) == s1.map(f) + s2.map(f)
{
    assert_sets_equal!((s1 + s2).map(f) == s1.map(f) + s2.map(f), y => {
        if s1.map(f).contains(y) {
            let x = choose |x| s1.contains(x) && f(x) == y;
            assert((s1 + s2).contains(x));
        } else if s2.map(f).contains(y) {
            let x = choose |x| s2.contains(x) && f(x) == y;
            assert((s1 + s2).contains(x));
        }
    });
}


}
