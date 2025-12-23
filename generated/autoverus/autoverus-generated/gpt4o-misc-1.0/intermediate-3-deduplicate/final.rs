#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

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
            nums@.subrange(0, (i) as int).to_set().ext_equal(res@.to_set()),
            res.len() <= i,
            res@.no_duplicates(),
            nums.len() == nums.len(),
    {
        let mut found = false;
        let mut j = 0;
        while j < res.len()
            invariant
                j <= res.len(),
                found == exists|k: int| 0 <= k < j && nums[i as int] == res[k] || !found,
                res.len() == res.len(),
                nums@.len() == nums.len(),
                res@.len() == res.len(),
                i >= 0,
                j >= 0,
                i < nums.len(),
        {
            if nums[i] == res[j] {
                found = true;
                break;
            }
            j += 1;
        }
        proof {
            if !found {
                assert(!exists|k: int| 0 <= k < j && nums[i as int] == res[k]);
            } else {
                assert(found == exists|k: int| 0 <= k < j && nums[i as int] == res[k]);
            }
        }
        if !found {
            res.push(nums[i]);
        }
        i += 1;
    }
    res
}

} // verus!
// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 3