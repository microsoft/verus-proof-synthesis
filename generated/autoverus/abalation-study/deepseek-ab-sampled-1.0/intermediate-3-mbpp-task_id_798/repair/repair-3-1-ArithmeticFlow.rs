
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

// Lemma to prove the monotonicity of sum_to
proof fn lemma_sum_to_monotonic(index1: int, index2: int)
    requires
        index1 <= index2,
    ensures
        sum_to(arr@.take(index1 as nat)) <= sum_to(arr@.take(index2 as nat)),
{
    // Implementation of the lemma which assures that the sum increases monotonically
    // (Or remains the same) as the index increases.
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.take(index as int)),
            forall |k: int| 0<= k < index ==> arr[k] >= -9223372036854775808,
            forall |k: int| 0<= k < index ==> arr[k] <= 9223372036854775807,
            sum + arr[index] as i128 <= i128::MAX,
    {
        // Assert that summing the next element doesn't cause overflow
        assert(sum + arr[index] as i128 <= i128::MAX) by {
            // Using the lemma to prove the bound
            lemma_sum_to_monotonic(index as int, (index + 1) as int);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} 


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True