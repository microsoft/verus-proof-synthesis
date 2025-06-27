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
            1 <= i <= nums.len(),
            nums.len() > 0,
            exists |j: int| 0 <= j < i ==> max == nums@.index(j),
            forall |k: int| 0 <= k < i ==> nums@.index(k) <= max,
    {
        if nums[i] > max {
            max = nums[i];
        }
        i += 1;
    }

    ret = max;
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1