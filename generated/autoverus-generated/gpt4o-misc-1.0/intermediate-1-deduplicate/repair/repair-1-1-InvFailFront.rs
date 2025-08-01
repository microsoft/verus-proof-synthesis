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
    proof {
        assert(i <= nums.len());
        assert(seq_to_set_rec(nums@.subrange(0, i as int)).ext_equal(res@.to_set()));
        assert(i < nums.len());
        assert(nums.len() == nums.len());
        assert(res.len() == res.len());
    } 
    while i < nums.len()
        invariant
            i <= nums.len(),
            res@.no_duplicates(),
            seq_to_set_rec(nums@.subrange(0, i as int)).ext_equal(res@.to_set()),
            i < nums.len(),
            nums.len() == nums.len(), // Loop invariant specifying the length of nums
            res.len() == res.len(),   // Loop invariant specifying the length of res
    {
        let mut found = false;
        let mut j = 0;
        while j < res.len()
            invariant
                !found ==> forall|k: int| 0 <= k < j ==> res[k as int] != nums[(i) as int],
                found ==> exists|k: int| 0 <= k < j && res[k as int] == nums[(i) as int],
                j <= res.len(),
                i < nums.len(),
                res.len() == res.len(),   // Loop invariant specifying the length of res
                nums.len() == nums.len(), // Loop invariant specifying the length of nums
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

//             i < nums.len(),
//   None: i < nums.len()

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 5
// Safe: True