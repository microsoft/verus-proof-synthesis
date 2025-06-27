#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {
fn linear_search(nums: Vec<i32>, target: i32) -> (ret: i32)
requires
    nums@.len() < 0x8000_0000,
ensures
    (ret < nums@.len() as i32 && ret >= 0 ==> nums@[ret as int] == target &&
        forall |i: int| 0 <= i < ret as int ==> #[trigger]nums@[i] != target) ||
    (ret == -1 ==> forall |i: int| 0 <= i < nums@.len() as int ==> #[trigger]nums@[i] != target),
{
    let mut i = 0;
    while i < nums.len()
    invariant
        0 <= i <= nums.len(),
        (i >= nums.len() ==> forall |k: int| 0 <= k < nums.len() as int ==> nums@[k] != target),
        (i < nums.len() ==> forall |k: int| 0 <= k < i as int ==> nums@[k] != target),
    {
        if nums[i] == target {
            break;
        }
        i = i + 1;
    }
    if i == nums.len() {
        -1
    } else {
        i as i32
    }
}
}
// Score: (2, 0)
// Safe: False