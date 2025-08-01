

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

fn abs_bound(x: i128) -> bool {
    i128::MIN <= x && x <= i128::MAX
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;
    let current_min_sum = 0i128;
    let current_max_sum = 0i128;
    
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            sum == sum_to(arr@.take((index) as int)),
            current_min_sum <= sum,
            sum <= current_max_sum,
            abs_bound(sum),
    {
        // Before updating the sum, check for overflow and underflow
        {
            // Track the bounds for the next element
            let current_value = arr[index] as i128;
            current_min_sum += current_value;
            current_max_sum += current_value;

            // Update bounds
            if current_min_sum < i128::MIN {
                current_min_sum = i128::MIN;
            }
            if current_max_sum > i128::MAX {
                current_max_sum = i128::MAX;
            }
            
            // Stronger assertions with new invariants
            assert(sum + current_value >= i128::MIN);
            assert(sum + current_value <= i128::MAX);
        }

        // Update the sum
        sum = sum + arr[index] as i128;
        index += 1;

        // Enforce bounds
        {
            current_min_sum = i128::MIN;
            current_max_sum = i128::MAX;
            assert(abs_bound(sum));
        }
    }
    sum
}

}

//         assert( sum + (arr[( index ) as int] as i128) >= i128::MIN );
//   assertion failed: sum + (arr[( index ) as int] as i128) >= i128::MIN

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False