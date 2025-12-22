use vstd::prelude::*;

fn main() {}

verus! {

fn smallest_num(nums: &Vec<i32>) -> (min: i32)
    requires
        nums.len() > 0,
    ensures
        forall|i: int| 0 <= i < nums.len() ==> min <= nums[i],
        exists|i: int| 0 <= i < nums.len() && min == nums[i],
{
    let mut min = nums[0];
    let mut index = 1;

    while index < nums.len() {
        if nums[index] < min {
            min = nums[index];
        }
        index += 1;
    }
    min
}

} // verus!
