
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

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;
    while index < arr.len()
        invariant
            index <= arr.len(),
            sum == sum_to(arr@.take(index as int)),
            index >= 0,
            arr.len() >= 0,
    {
        // Assertion to prevent overflow/underflow
        assert!(is_sum_safe(sum, arr[index] as i128), "Arithmetic overflow/underflow detected");

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

// Helper function to check if the sum is within safe bounds
lemma fn is_sum_safe(current_sum: i128, value_to_add: i128) -> bool
    ensures
        result == (current_sum + value_to_add <= i128::MAX && current_sum + value_to_add >= i128::MIN),
{
    current_sum + value_to_add <= i128::MAX && current_sum + value_to_add >= i128::MIN
}
}


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False