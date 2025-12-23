
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

// Lemma function to prove the monotonicity
proof fn lemma_monotonic(arr: Seq<i64>, index: nat)
    ensures
        sum_negative_to(arr.subrange(0, index)) <= sum_negative_to(arr.subrange(0, index + 1))
{
    if index > 0 {
        lemma_monotonic(arr, (index - 1) as nat);
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
            let arr_elem = arr[index] as i128;
            // Assertion to avoid arithmetic overflow/underflow
            assert!(sum_neg + arr_elem >= i128::MIN && sum_neg + arr_elem <= i128::MAX) by {
                lemma_monotonic(arr@, index as nat);
            };
            sum_neg = sum_neg + arr_elem;
        }
        index += 1;
    }
    sum_neg
}

} // verus!


//             sum_neg = sum_neg + (arr[index] as i128);
//   None: sum_neg + (arr[index] as i128)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False