
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
            // Ensure next sum is within i128 bounds
            sum + (arr[index] as i128) <= i128::MAX,
            sum + (arr[index] as i128) >= i128::MIN,
    {
        // Check that adding the next element won't cause overflow/underflow
        assert!(sum + (arr[index] as i128) <= i128::MAX);
        assert!(sum + (arr[index] as i128) >= i128::MIN);

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False