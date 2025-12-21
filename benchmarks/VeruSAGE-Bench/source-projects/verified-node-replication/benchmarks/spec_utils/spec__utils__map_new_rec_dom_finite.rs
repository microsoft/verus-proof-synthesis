use vstd::prelude::*;

fn main() {}

verus!{

// File: spec/utils.rs
pub open spec fn map_new_rec<V>(dom: nat, val: V) -> Map<nat, V>
    decreases dom,
    when dom >= 0
{
    if dom == 0 {
        map![ dom => val]
    } else {
        map_new_rec((dom - 1) as nat, val).insert(dom, val)
    }
}

pub proof fn map_new_rec_dom_finite<V>(dom: nat, val: V)
    ensures
        map_new_rec(dom, val).dom().finite(),
        forall|n: nat| 0 <= n <= dom <==> map_new_rec(dom, val).contains_key(n),
        forall|n|
            (#[trigger] map_new_rec(dom, val).contains_key(n)) ==> map_new_rec(dom, val)[n] == val,
    decreases dom,
{
    if dom == 0 {
    } else {
        let sub_dom = (dom - 1) as nat;
        let sub_map = map_new_rec(sub_dom as nat, val);
        assert(sub_map.dom().finite()) by {
            map_new_rec_dom_finite(sub_dom, val);
        }
        assert(forall|n: nat| (#[trigger] sub_map.contains_key(n)) <==> 0 <= n <= sub_dom) by {
            map_new_rec_dom_finite(sub_dom, val);
        }
        assert(forall|n: nat| (#[trigger] sub_map.contains_key(n)) ==> sub_map[n] == val) by {
            map_new_rec_dom_finite(sub_dom, val);
        }
    }
}


}
