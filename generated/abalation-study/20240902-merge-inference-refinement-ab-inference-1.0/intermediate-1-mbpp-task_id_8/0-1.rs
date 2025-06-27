use vstd::prelude::*;

fn main() {}

verus! {

fn square_nums(nums: &Vec<i32>) -> (squared: Vec<i32>)
    requires
        forall|k: int|
            0 <= k < nums.len() ==> (0 <= #[trigger] nums[k] * #[trigger] nums[k] < i32::MAX),
    ensures
        nums.len() == squared.len(),
        forall|k: int| 0 <= k < nums.len() ==> (#[trigger] squared[k] == nums[k] * nums[k]),
{
    let mut result: Vec<i32> = Vec::new();
    let mut index = 0;

    while index < nums.len()
        invariant
            index <= nums.len(),
            result.len() == index,
            forall|k: int| 0 <= k < index ==> result[k] == nums[k] * nums[k],
            forall|k: int| 0 <= k < nums.len() ==> (0 <= nums[k] * nums[k] < i32::MAX),
    {
        result.push(nums[index] * nums[index]);
        index += 1
    }
    result
}

} // verus!

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1