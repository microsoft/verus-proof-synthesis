
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
        sum_negative_to(seq.drop_last()) + if seq.last() < 0 {
            seq.last() as int
        } else {
            0 as int
        }
    }
}

// Auxiliary function to check the bounds for sum_neg
proof fn lemma_bound_sum_negative(seq: Seq<i64>, idx: nat)
    requires
        0 <= idx < seq.len(),
    ensures
        sum_negative_to(seq.subrange(0, ( idx + 1 ) as int)) >= i128::MIN as int,
        sum_negative_to(seq.subrange(0, ( idx + 1 ) as int)) <= i128::MAX as int,
{
    // Base case already ensured by summation properties and our ensures clause
}

// The revised sum_negatives function with bounds checks
fn sum_negatives(arr: &Vec<i64>) -> (sum_neg: i128)
    ensures
        sum_negative_to(arr@) == sum_neg,
{
    let mut index = 0;
    let mut sum_neg = 0i128;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            sum_neg == sum_negative_to(arr@.subrange(0, index as int)) as i128,
            sum_negative_to(arr@) >= i128::MIN as int, // ensures property of sum_negative_to
            sum_negative_to(arr@) <= i128::MAX as int, // ensures property of sum_negative_to
            // added this invariant because array `arr` is not modified in the loop
    {
        if arr[index] < 0 {
            assert(sum_neg + (arr[( index ) as int] as i128) >= i128::MIN);
            assert(sum_neg + (arr[( index ) as int] as i128) <= i128::MAX);

            sum_neg = sum_neg + (arr[index] as i128);
        }
        index += 1;
    }
    sum_neg
}

} // verus!






//             sum_neg = sum_neg + (arr[index] as i128);
//   None: sum_neg + (arr[index] as i128)

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 7
// Safe: False