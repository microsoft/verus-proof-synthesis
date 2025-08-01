
use vstd::prelude::*;

fn main() {}

verus! {

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

proof fn lemma_monotonic(seq: Seq<i64>, index: nat)
    requires
        index < seq.len(),
    ensures
        sum_negative_to(seq.subrange(0, ( index + 1 ) as int)) >= sum_negative_to(seq.subrange(0, ( index ) as int)),
    decreases seq.len() - index
{
    if index > 0 {
        lemma_monotonic(seq, ( index - 1 ) as nat);
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
            index <= arr.len(),
            sum_neg == sum_negative_to(arr@.subrange(0, index as int)) as i128,
            index < arr.len(), // Upper bound copied from the function pre-condition
            arr.len() == arr.len(), // Loop invariant specifying the length of the array
    {
        if arr[index] < 0 {
            let next_sum_neg = sum_neg + (arr[index] as i128);
            assert(next_sum_neg <= (i128::MAX as i128)); // Check for overflow
            assert(next_sum_neg >= (i128::MIN as i128)); // Check for underflow
            sum_neg = next_sum_neg;
        }
        index += 1;
    }
    sum_neg
}

} // verus!





//             sum_neg = sum_neg + (arr[index] as i128);
//   None: sum_neg + (arr[index] as i128)

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 6
// Safe: False