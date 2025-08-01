#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

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
            0 <= i <= nums.len(),
            1 <= nums.len(),
            exists|j: int| 0 <= j < i ==> nums[j] == max,
            forall|j: int| 0 <= j < i ==> nums[j] <= max,
            i <= nums.len(),
            nums.len() > 0,
    {
        if nums[i] > max {
            max = nums[i];
        }
        i += 1;
    }
    max
}

} // verus!

// Score: (0, 2)
// Safe: True