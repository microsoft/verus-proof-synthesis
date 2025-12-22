#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::set::*;
use vstd::set_lib::*;

fn main() {}

verus! {

pub proof fn lemma_mk_map_insert_k<A, B>(m: Set<A>, k: A, map: spec_fn(A) -> B)
    ensures m.insert(k).mk_map(map) == m.mk_map(map).insert(k, map(k)),
{
    assert(m.insert(k).mk_map(map).contains_pair(k, map(k)));
    assert(m.insert(k).mk_map(map) =~= m.mk_map(map).insert(k, map(k))) by {
        assert forall |key: A| #[trigger] m.insert(k).mk_map(map).contains_key(key) implies m.mk_map(map).insert(k, map(k)).contains_key(key) by {
            if key == k {
                assert(m.mk_map(map).insert(k, map(k)).contains_key(k));
            } else {
                assert(m.mk_map(map).contains_key(key));
            }
        }
        assert forall |key: A| #[trigger] m.mk_map(map).insert(k, map(k)).contains_key(key) implies m.insert(k).mk_map(map).contains_key(key) by {
            if key == k {
                assert(m.insert(k).mk_map(map).contains_key(k));
            } else {
                assert(m.mk_map(map).contains_key(key));
            }
        }
    }
}

}
