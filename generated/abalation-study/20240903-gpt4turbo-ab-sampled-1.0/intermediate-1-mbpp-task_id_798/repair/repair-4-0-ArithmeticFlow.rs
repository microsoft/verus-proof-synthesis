
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
    // Placeholder for proof logic
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
            arr.len() == arr@.len(), // Loop invariant for the length of the array
    {
        // Assert that adding the next element won't cause overflow or underflow
        // Note: This assumes lemma_sum_to_bounds proves sum_to within i128 bounds.
        assert!(sum + arr[index] as i128 >= i128::MIN && sum + arr[index] as i128 <= i128::MAX);
        
        sum = sum + arr[index] as i128;
        index += 1;
        proof {
            lemma_sum_to_bounds(arr@.subrange(0, index as int)); // Ensure this proof adjusts for correctness
        }
    }
    sum
}

}


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False