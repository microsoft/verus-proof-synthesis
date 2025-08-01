
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}
verus! {

fn linear_search(nums: Vec<i32>, target: i32) -> (ret: i32)
    requires
        nums@.len() < 0x8000_0000,
    ensures
        ret < nums@.len(),
        ret >= 0 ==> nums@[ret as int] == target,
        ret >= 0 ==> forall|i: int| 0 <= i < ret as int ==> # [trigger] nums@[i] != target,
        ret < 0 ==> forall|i: int| 0 <= i < nums@.len() as int ==> # [trigger] nums@[i] != target,
{
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            0 <= i as int <= nums@.len(),
            forall|j: int| 0 <= j < nums.len() ==> nums@[j] == nums@[j], // Modified to cover every element since nums is not changed in the loop
            forall|j: int| 0 <= j < i ==> nums@[j] != target,
            forall|j: int| 0 <= j < i as int ==> nums@[j] != target,
            i <= nums.len(),
            i as int <= nums@.len(),
            nums@.len() < 0x8000_0000,
            nums.len() == nums.len(),
    {
        if nums[i] == target {
            break ;
        }
        i = i + 1;
    }
    if i == nums.len() {
        -1
    } else {
        i as i32
    }
}

} // verus!
