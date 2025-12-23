use vstd::prelude::*;
fn main() {}
verus!{
pub fn remove_all_greater(v: &mut Vec<i32>, e: i32) -> (curr_vlen: usize)
    requires
        forall |k1:int,k2:int| 0 <= k1 < k2 < old(v).len() ==> old(v)[k1] != old(v)[k2]
    ensures
        forall |k:int| 0 <= k < curr_vlen ==> v[k] <= e && (exists |q:int| 0 <= q < old(v).len() && v[k] == old(v)[q]),
        forall |k:int| 0 <= k < old(v).len() && old(v)[k] <= e ==> (exists |q:int| 0 <= q < curr_vlen && v[q] == old(v)[k]),
{
    let mut i: usize = 0;
    let old_vlen = v.len();
    let mut curr_vlen = old_vlen;
    while (i < curr_vlen)
    {
        if (v[i] > e) {
            let mut j: usize = i;
            while (j < curr_vlen - 1)
            {
                v.set(j, v[j + 1]);
                j = j + 1;
            }
            curr_vlen = curr_vlen - 1;
        }
        else {
            i = i + 1;
        }
    }
    curr_vlen
}
}
