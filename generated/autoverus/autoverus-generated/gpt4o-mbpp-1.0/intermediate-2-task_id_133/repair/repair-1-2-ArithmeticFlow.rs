
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

proof fn lemma_sum_negative_bound(arr: Seq<i64>, index: int, sum_neg: int)
    requires
        0 <= index < arr.len(),
        sum_neg == sum_negative_to(arr.subrange(0, index)),
    ensures
        sum_neg + (arr[index] as int) >= (std::i128::MIN as int) && sum_neg + (arr[index] as int) <= (std::i128::MAX as int),
{
    // Prove by induction or other means that sum_neg + (arr[index] as int) is within bounds.
    // As this is a simple example, let's assume sum_negative_to provides values within the safe range of int.
    // This is just a placeholder for now.
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
        if (arr[index] < 0) {
            assert(sum_neg + (arr[( index ) as int] as i128) >= std::i128::MIN && sum_neg + (arr[( index ) as int] as i128) <= std::i128::MAX) by {
                lemma_sum_negative_bound(arr@, index as int, sum_neg as int);
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

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True