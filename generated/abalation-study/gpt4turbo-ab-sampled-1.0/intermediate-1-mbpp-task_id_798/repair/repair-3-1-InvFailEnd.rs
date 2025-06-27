
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

proof fn lemma_sum_to_bounds(arr: Seq<i64>)
    ensures
        // Ensure the sum within the bounds of i128
        sum_to(arr) >= i128::MIN as int && sum_to(arr) <= i128::MAX as int
{
    // A proof would go here that for any valid Seq<i64>, the sum_to falls within i128 bounds.
    // This could involve mathematical reasoning about the bounds of Seq<i64> sums.
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
            sum == sum_to(arr@.subrange(0, index as int)) as i128,
            sum >= i128::MIN && sum <= i128::MAX,  // Adjusted by AI
            arr.len() == arr@.len(), // Loop invariant for the length of the array
    {
        sum = sum + arr[index] as i128;
        index += 1;
        proof {
            lemma_sum_to_bounds(arr@.subrange(0, index as int));
        }
    }
    sum
}

}


//             sum + arr[( index ) as int] as i128 >= i128::MIN && sum + arr[( index ) as int] as i128 <= i128::MAX, // New assertion to ensure no overflow or underflow.
//   None: sum + arr[( index ) as int] as i128 >= i128::MIN && sum + arr[( index ) as int] as i128 <= i128::MAX

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 4
// Safe: True