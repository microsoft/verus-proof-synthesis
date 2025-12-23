use vstd::prelude::*;
fn main() {}
verus!{


fn remove_all_greater(v: &mut Vec<i32>, e: i32) -> (curr_vlen: usize)
    requires
        forall |k1:int,k2:int| 0 <= k1 < k2 < old(v).len() ==> old(v)[k1] != old(v)[k2]
    ensures
        curr_vlen == v.len(),
        forall |k:int| 0 <= k < v.len() ==> v[k] <= e && old(v)@.contains(v[k]),
        forall |k:int| 0 <= k < old(v).len() && old(v)[k] <= e ==> v@.contains(old(v)[k]),
{
    let mut i: usize = 0;
    let old_vlen = v.len();
    let mut curr_vlen = old_vlen;

     while (i < curr_vlen)
        invariant
            curr_vlen == v.len(),
            forall |k:int| 0 <= k < i ==> v[k] <= e,
            forall |k:int| 0 <= k < curr_vlen ==> old(v)@.contains(v[k]),
            forall |k:int| 0 <= k < old(v).len() && old(v)[k] <= e ==> v@.contains(old(v)[k]),
    {
        if (v[i] > e) {
            let ghost oldv=v@;
            v.remove(i);
            assert(forall |k:int| 0 <= k < i ==> oldv[k] == v[k]);
            assert(forall |k:int| i < k < oldv.len() ==> oldv[k] == v[k-1]);
            curr_vlen -= 1;
        } else {
            i += 1;
        }

    }
    curr_vlen
}
}
