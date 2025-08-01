#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}
verus! {

fn find_max(nums: Vec<i32>) -> (ret: i32)
    requires
        nums.len() > 0,
    ensures
        forall|i: int| 0 <= i < nums@.len() ==> nums@[i] <= ret,
        exists|i: int| 0 <= i < nums@.len() ==> nums@[i] == ret,
{
    let mut max = nums[0];
    let mut i = 1;
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            1 <= nums.len(),
            forall|j: int| 0 <= j < i ==> nums@[j] <= max,
    {
        if nums[i] > max {
            max = nums[i];
        }
        i += 1;
    }
    max
}

} // verus!



// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1