use vstd::prelude::*;

fn main() {}
pub type NodeId = nat;

verus!{

// File: spec/utils.rs
pub open spec fn map_contains_value<K, V>(
    map: Map<K, V>,
    val: V,
) -> bool
{
    exists|i: K| #[trigger] map.contains_key(i) && map.index(i) == val
}


// File: spec/cyclicbuffer.rs
pub open spec fn min(x: nat, y: nat) -> nat {
    if x < y {
        x
    } else {
        y
    }
}

pub open spec fn map_min_value(m: Map<NodeId, nat>, idx: nat) -> nat
    decreases idx,
{
    if idx === 0 {
        m.index(0)
    } else {
        min(map_min_value(m, (idx - 1) as nat), m.index(idx))
    }
}

proof fn map_min_value_smallest(m: Map<NodeId, nat>, idx: nat)
    requires
        forall|i| 0 <= i <= idx ==> m.contains_key(i),
    ensures
        forall|n| 0 <= n <= idx as nat ==> map_min_value(m, idx) <= m.index(n),
        map_contains_value(m, map_min_value(m, idx)),
{
}


}
