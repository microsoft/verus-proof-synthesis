#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {
    fn linear_search(nums: Vec<i32>) -> (ret: i32)
        requires
            nums@.len() < 100,
            forall |k:int| 0<= k < nums.len() ==> 0<= #[trigger] nums[k] < 10,
            ensures
                ret <= 100,
    {
        let mut i = 0;
        let mut sum = 0;
        while i < nums.len()
            invariant
                forall |k:int| 0<= k < nums.len() ==> 0<= #[trigger] nums[k] < 10,
                sum <= 100,
                i <= nums.len(),
        {
            if sum + nums[i] > 100 {
                break;
            }

            sum = sum + nums[i];
            i = i + 1;
        }
        assert(i == nums.len() || sum + nums[i as int] > 100);
        sum
    }
}
