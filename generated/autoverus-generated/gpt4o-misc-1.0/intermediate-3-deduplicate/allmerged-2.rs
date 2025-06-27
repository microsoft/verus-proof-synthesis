#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}
verus! {

spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len(),
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
        nums@.to_set().ext_equal(res@.to_set()),
{
    let mut res = Vec::new();
    let mut i = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            nums.len() < 1000,
            nums@.subrange(0, (i) as int).to_set().ext_equal(res@.to_set()),
            res.len() <= i,
            res.len() <= nums.len(),
            res@.no_duplicates(),
            seq_to_set_rec(nums@.subrange(0, i as int)).ext_equal(res@.to_set()),
    {
        let mut found = false;
        let mut j = 0;
        while j < res.len()
            invariant
                found == exists|k: int| 0 <= k < j && nums[(i) as int] == res[k],
                found == exists|k: int| 0 <= k < j && res[k] == nums[(i) as int],
                i <= nums.len(),
                j <= res.len(),
                nums.len() < 1000,
                res@.no_duplicates(),
                seq_to_set_rec(nums@.subrange(0, i as int)).ext_equal(res@.to_set()),
        {
            if nums[i] == res[j] {
                found = true;
                break ;
            }
            j += 1;
        }
        if !found {
            res.push(nums[i]);
        }
        i += 1;
    }
    res
}

} // verus!


// Score: Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 8