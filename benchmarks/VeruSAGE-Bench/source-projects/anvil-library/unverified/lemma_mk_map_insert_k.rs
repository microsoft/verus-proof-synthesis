#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::set::*;
use vstd::set_lib::*;

fn main() {}

verus! {

pub proof fn lemma_mk_map_insert_k<A, B>(m: Set<A>, k: A, map: spec_fn(A) -> B)
    ensures m.insert(k).mk_map(map) == m.mk_map(map).insert(k, map(k)),
{
}

}
