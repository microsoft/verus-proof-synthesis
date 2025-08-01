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
            res@.no_duplicates(),
            seq_to_set_rec(nums@.subrange(0, i as int)).ext_equal(res@.to_set()),
            nums.len() == nums.len()
    {
        let mut found = false;
        let mut j = 0;
        while j < res.len()
            invariant
                j <= res.len(),
                i < nums.len(),
                found == exists|k: int| 0 <= k < j && nums[i as int] == res[k] || !found,
                res@.no_duplicates()
        {
            if nums[i] == res[j] {
                found = true;
                proof {
                    assert(found == exists|k: int| 0 <= k < j && nums[i as int] == res[k] || !found);
                }
                break;
            }
            j += 1;
        }
        if !found {
            res.push(nums[i]);
            proof {
                assert(found == exists|k: int| 0 <= k < j && nums[i as int] == res[k] || !found);
            }
        }
        i += 1;
    }
    res
}

} // verus!

//                 found == exists|k: int| 0 <= k < j && nums[i as int] == res[k] || !found,
//   None: found == exists|k: int| 0 <= k < j && nums[i as int] == res[k] || !found

// Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 4
// Safe: True