#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
fn find_max(nums: Vec<i32>) -> (ret:i32)
requires
    nums.len() > 0,
ensures
    forall |i: int| 0 <= i < nums@.len() ==> nums@[i] <= ret,
    exists |i: int| 0 <= i < nums@.len() ==> nums@[i] == ret,
{
    let mut max = nums[0];
    let mut i = 1;

    while i < nums.len()
        invariant
            1 <= nums.len(),
            0 <= i <= nums.len(),
            exists |k: int| 0 <= k < i && nums[k] == max,
            forall |j: int| 0 <= j < i ==> nums[j] <= max,
    {
        if nums[i] > max {
            max = nums[i];
        }
        i += 1;
    }
    max
}
}

// Score: (2, 0)
// Safe: True