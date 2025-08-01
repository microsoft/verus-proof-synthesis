
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {
    #[verifier::loop_isolation(false)]

    spec fn sum_to(arr: Seq<i64>) -> int
        decreases arr.len(),
    {
        if arr.len() == 0 {
            0
        } else {
            sum_to(arr.drop_last()) + arr.last()
        }
    }

    proof fn lemma_sum_monotonic(pfx: Seq<i64>, idx: int)
        requires
            0 <= idx <= pfx.len(),
        ensures
            sum_to(pfx.subrange(0, idx)) + pfx.index(idx) <= sum_to(pfx.subrange(0, idx + 1)),
    {
        // The function is defined recursively and pfx.idx is added once
    }

    fn sum(arr: &Vec<i64>) -> (sum: i128)
        ensures
            sum_to(arr@) == sum,
    {
        let mut index = 0;
        let mut sum = 0i128;
        while index < arr.len()
            invariant
                index <= arr.len(),
                sum_to(arr@.subrange(0, index as int)) == sum as int,
                index < arr.len(),
                arr.len() == arr.len(),  // Invariant specifying the length of the array
        {
            // Adding assertion to check bounds before the arithmetic operation
            assert(sum + arr[( index ) as int] as i128 <= i128::MAX && sum + arr[( index ) as int] as i128 >= i128::MIN) by {
                lemma_sum_monotonic(arr@, index as int);
            };

            sum = sum + arr[index] as i128;
            index += 1;
        }
        sum
    }
} 




//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 5
// Safe: False