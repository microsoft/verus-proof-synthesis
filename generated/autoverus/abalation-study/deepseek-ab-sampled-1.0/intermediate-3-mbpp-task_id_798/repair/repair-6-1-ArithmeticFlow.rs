
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

proof fn lemma_sum_to_monotonic(index: usize, arr: Seq<i64>)
    requires
        index < arr.len(),
    ensures
        sum_to(arr.take(index as int)) <= sum_to(arr.take((index + 1) as int))
{
    // Prove that adding the next element increases or maintains the sum.
    // This leverages the fact that each element contributes to the sum.
    proof {
        if index < arr.len() as usize {
            lemma_sum_to_monotonic(index, arr);
        }
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
            0 <= index <= arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.take(index as int)),
            forall |k: int| 0<= k < index ==> arr[k] >= -9223372036854775808,  // assuming i64 bounds; array not modified via x.set()
            forall |k: int| 0<= k < index ==> arr[k] <= 9223372036854775807,   // assuming i64 bounds; array not modified via x.set()
    {
        assert(sum + arr[index] as i128 <= 9223372036854775807i128 * (index + 1) as i128) by {
            lemma_sum_to_monotonic(index as usize, arr@.take(index as int));
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True