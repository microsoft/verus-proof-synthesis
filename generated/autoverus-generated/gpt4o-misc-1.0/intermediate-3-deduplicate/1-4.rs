#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len()
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}


fn remove_duplicates(nums: Vec<i32>) -> (res: Vec<i32>)
ensures
    res@.no_duplicates(),
    nums@.to_set().ext_equal(res@.to_set())
{
    let mut res = Vec::new();
    let mut i = 0;

    while i < nums.len()
        invariant
            i <= nums.len(),
            res.len() <= i,
            res@.no_duplicates(),
            nums@.take(i).to_set() == res@.to_set()
    {
        let mut found = false;
        let mut j = 0;

        while j < res.len()
            invariant
                j <= res.len(),
                found ==> exists |k: int| 0 <= k < j && nums[i] == res[k],
                !found ==> forall |k: int| 0 <= k < j ==> nums[i] != res[k]
        {
            if nums[i] == res[j] {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            res.push(nums[i]);
            assert(nums@.index(i) == nums[i] && nums[i] !in res@.drop_last());
        }
        i += 1;
    }
    res
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1