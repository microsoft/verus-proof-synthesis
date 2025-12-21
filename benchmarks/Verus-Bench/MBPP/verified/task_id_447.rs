use vstd::prelude::*;

fn main() {
    // Write a function in Rust to find cubes of individual elements in a list.

    assert_eq!(
        cube_element(&vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]),
        [1, 8, 27, 64, 125, 216, 343, 512, 729, 1000]
    );
    assert_eq!(cube_element(&vec![10, 20, 30]), [1000, 8000, 27000]);
    assert_eq!(cube_element(&vec![12, 15]), [1728, 3375]);
}

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
        invariant
            cubed_array@.len() == i,
            forall|k: int|
                0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                    <= i32::MAX),
            forall|k: int|
                0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                    * #[trigger] nums[k] <= i32::MAX),
            forall|k: int|
                0 <= k < i ==> (#[trigger] cubed_array[k] == nums[k] * nums[k] * nums[k]),
    {
        cubed_array.push(nums[i] * nums[i] * nums[i]);
        i += 1;
    }
    cubed_array
}

} // verus!
