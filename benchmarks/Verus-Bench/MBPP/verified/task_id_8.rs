use vstd::prelude::*;

fn main() {
    //Write a function in Rust to find squares of individual elements in a list.

    assert_eq!(
        square_nums(&vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]),
        [1, 4, 9, 16, 25, 36, 49, 64, 81, 100]
    );
    assert_eq!(square_nums(&vec![10, 20, 30]), [100, 400, 900]);
    assert_eq!(square_nums(&vec![12, 15]), [144, 225]);
}

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
            0 <= index <= nums.len(),
            result@.len() == index,
            forall|k: int|
                0 <= k < nums.len() ==> (0 <= #[trigger] nums[k] * #[trigger] nums[k] < i32::MAX),
            forall|k: int| 0 <= k < index ==> (#[trigger] result[k] == nums[k] * nums[k]),
    {
        result.push(nums[index] * nums[index]);
        index += 1
    }
    result
}

} // verus!
