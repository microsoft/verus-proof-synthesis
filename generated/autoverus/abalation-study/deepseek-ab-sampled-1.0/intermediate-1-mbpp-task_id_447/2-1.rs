

use vstd::prelude::*;

fn main() {}

verus! {

fn cube_element(nums: &Vec<i32>) -> (cubed: Vec<i32>)
    requires
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                <= i32::MAX),
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                * #[trigger] nums[k] <= i32::MAX),
    ensures
        forall|i: int|
            0 <= i < nums.len() ==> cubed[i] == #[trigger] nums[i] * #[trigger] nums[i]
                * #[trigger] nums[i],
{
    let mut cubed_array: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < nums.len()
    {
        invariant
            0 <= i <= nums.len(),
            cubed_array.len() == i,
            forall |k: int| 0 <= k < i ==> cubed_array[k] == nums[k] * nums[k] * nums[k],
        {
            let current_num = nums[i];
            let cube = current_num * current_num * current_num;
            cubed_array.push(cube);
            i += 1;
        }
    }
    cubed_array
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1