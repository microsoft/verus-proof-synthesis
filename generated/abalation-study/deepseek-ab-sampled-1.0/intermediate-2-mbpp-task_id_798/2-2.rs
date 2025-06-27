

use vstd::prelude::*;
fn main() {}
verus! {
    spec fn sum_to(arr: Seq<i64>) -> int
        decreases arr.len(),
    {
        if arr.len() == 0 {
            0
        } else {
            sum_to(arr.drop_last()) + arr.last()
        }
    }

    fn sum(arr: &Vec<i64>) -> (sum: i128)
        ensures
            sum_to(arr@) == sum,
    {
        let mut index = 0;
        let mut sum = 0i128;

        proof {
            // Establish the base case of the invariant
            assert(sum == 0);
            assert(index == 0);
        }

        let arr_len = arr.len();
        while index < arr_len
            invariant 
                index <= arr_len,
                sum == sum_to(arr@.subrange(0, index as int)),
        {
            sum = sum + arr[index] as i128;
            index += 1;

            proof {
                // Prove the invariant step: after adding arr[index], sum equals sum_to up to index+1
                assert(sum == sum_to(arr@.subrange(0, index as int)));
            }
        }

        // Final step: after loop termination, index == arr_len
        proof {
            assert(index == arr_len);
            // Therefore, sum == sum_to(arr@.subrange(0, arr_len as int)) == sum_to(arr@)
        }

        sum
    }
}
// is safe: False
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4