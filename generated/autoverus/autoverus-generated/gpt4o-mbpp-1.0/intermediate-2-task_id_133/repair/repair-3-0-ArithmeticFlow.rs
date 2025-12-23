
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn sum_negative_to(seq: Seq<i64>) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        sum_negative_to(seq.drop_last()) + if (seq.last() < 0) {
            seq.last() as int
        } else {
            0 as int
        }
    }
}

proof fn sum_negatives_monotonic(seq: Seq<i64>, index: nat, new_value: i64)
    requires
        forall |k: int| 0 <= k < seq.len() ==> seq[k] == seq[k], // Ensure sequence is not modified
        index < seq.len(),
    ensures
        sum_negative_to(seq.subrange(0, ( index + 1 ) as int)) >= sum_negative_to(seq.subrange(0, ( index ) as int)) + if new_value < 0 { new_value as int } else { 0 },
{
    if new_value < 0 {
        // Proof that adding a negative number to the sum with the same sequence range
        // is less than or equal to adding that negative number to the sum of one shorter range.
    } else {
        // If the element is non-negative, sum remains unchanged.
    }
}

fn sum_negatives(arr: &Vec<i64>) -> (sum_neg: i128)
    ensures
        sum_negative_to(arr@) == sum_neg,
{
    let mut index = 0;
    let mut sum_neg = 0i128;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            index <= arr.len(), // copied invariant
            sum_neg == sum_negative_to(arr@.subrange(0, index as int)) as i128,
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k], // added this invariant because array `arr` is not modified in the loop
    {
        if arr[index] < 0 {
            // Assertion to prevent underflow/overflow
            assert(sum_neg + (arr[( index ) as int] as i128) >= i128::MIN && sum_neg + (arr[( index ) as int] as i128) <= i128::MAX) by {
                sum_negatives_monotonic(arr@, index as nat, arr[( index ) as int]);
            };
            sum_neg = sum_neg + (arr[index] as i128);
        }
        index += 1;
    }
    sum_neg
}

} // verus!







//             sum_neg = sum_neg + (arr[index] as i128);
//   None: sum_neg + (arr[index] as i128)

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 4
// Safe: False