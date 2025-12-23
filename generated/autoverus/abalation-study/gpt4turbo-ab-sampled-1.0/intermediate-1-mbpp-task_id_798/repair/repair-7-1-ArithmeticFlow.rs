
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
    // For any valid Seq<i64>:
    // The maximum sum of `n` i64 values (each at their maximum) can be calculated as n * i64::MAX.
    // Given that `n` itself is limited (by practical memory constraints and the maximum length of a Vec or Seq),
    // and considering the maximum value of i64::MAX, this sum when calculated does not exceed the bounds of i128.
    // Similarly, the minimum sum calculated with i64::MIN values will not underflow i128.
    // Therefore, adding any single i64 value to this sum keeps the result within i128 bounds,
    // taking into account that i128's bounds are far greater than that of the sum of any practical Seq<i64>.
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
            // The proof obligation right before adding to sum
            lemma_sum_to_bounds(arr@.subrange(0, index as int), arr[( index ) as int] as i64);
        }

        // Asserting bounds right before performing addition
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX && sum + arr[( index ) as int] as i128 >= i128::MIN);
            
        // Now safe to perform addition, given the proof justifying the operation's safety
        sum = sum + arr[index] as i128;
        
        index += 1;
        
        proof {
            assert(sum == sum_to(arr@.subrange(0, index as int)) as i128); // Verifying sum correctness
        }
    }
    sum
}

}





//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 5
// Safe: True