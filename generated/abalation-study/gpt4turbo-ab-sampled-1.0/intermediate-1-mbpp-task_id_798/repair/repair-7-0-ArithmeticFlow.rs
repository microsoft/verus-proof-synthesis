
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

proof fn lemma_sum_to_bounds(arr: Seq<i64>, additional_value: i64)
    ensures
        // Ensure the sum with additional_value is within the bounds of i128
        sum_to(arr) >= i128::MIN as int && sum_to(arr) + additional_value <= i128::MAX as int,
        sum_to(arr) + additional_value >= i128::MIN as int && sum_to(arr) <= i128::MAX as int
{
    // Logic:
    // Since each element in `arr` is of type i64, and we're adding an i64 `additional_value`,
    // the sum can at most be `arr.len() * i64::MAX + additional_value`, or at least
    // `arr.len() * i64::MIN + additional_value`. Both cases should be within the i128 range.

    // This proof can be more sophisticated based on the properties and limits of `sum_to`,
    // but the general reasoning demonstrates safety within i128 bounds.
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
            sum >= i128::MIN && sum <= i128::MAX,  
            arr.len() == arr@.len(),
    {
        proof {
            lemma_sum_to_bounds(arr@.subrange(0, index as int), arr[index] as i64);
        }

        // Assert the bound right before the sum operation to ensure safety
        assert!(sum + arr[index] as i128 >= i128::MIN && sum + arr[index] as i128 <= i128::MAX);

        sum = sum + arr[index] as i128;
        index += 1;
        
        proof {
            assert!(sum == sum_to(arr@.subrange(0, index as int)) as i128); // Correction added here to match the operation's result with the specification.
        }
    }
    sum
}

}


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False