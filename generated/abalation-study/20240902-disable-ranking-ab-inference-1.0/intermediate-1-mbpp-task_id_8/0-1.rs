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
            // Safety invariant for the multiplication
            forall|i: int| 0 <= i < index ==> nums[i] * nums[i] >= 0,
            forall|i: int| 0 <= i < index ==> nums[i] * nums[i] < i32::MAX,
            // Ensures the result array contains squared values
            forall|i: int| 0 <= i < index ==> result[i] == nums[i] * nums[i],
    {
        result.push(nums[index] * nums[index]);
        index += 1;
    }
    
    result
}

} // verus!
// is safe: False
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 4