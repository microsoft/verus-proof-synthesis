
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
    // Add your mathematical reasoning proof here that for any valid Seq<i64> and an additional i64 value,
    // the sum including the additional value falls within i128 bounds.
    // This could involve demonstrating that the sum of i64 values cannot exceed/outstrip the capacity of i128.
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
            sum >= i128::MIN && sum <= i128::MAX,  
            arr.len() == arr@.len(),
    {
        proof {
            // The proof obligation right before adding to sum
            lemma_sum_to_bounds(arr@.subrange(0, index as int), arr[( index ) as int]);
        }
        
        // Now safe to perform addition, given the proof justifying the operation's safety
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

}



//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 4
// Safe: True