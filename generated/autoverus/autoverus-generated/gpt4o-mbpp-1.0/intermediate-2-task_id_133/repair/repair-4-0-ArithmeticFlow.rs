
use vstd::prelude::*;
fn main() {}

verus! {

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

proof fn lemma_sum_negative_to_monotonic(seq: Seq<i64>, len1: nat, len2: nat)
    requires
        0 <= len1 <= seq.len(),
        0 <= len2 <= seq.len(),
        len1 <= len2,
    ensures
        sum_negative_to(seq.subrange(0, ( len1 ) as int)) <= sum_negative_to(seq.subrange(0, ( len2 ) as int))
{
    // Monotonicity proof for the spec function `sum_negative_to`
    if len1 < len2 {
        lemma_sum_negative_to_monotonic(seq, len1, ( len2 - 1 ) as nat);
        assert(sum_negative_to(seq.subrange(0, len2 - 1)) <= sum_negative_to(seq.subrange(0, ( len2 ) as int)));
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
        if (arr[index] < 0) {
            assert(sum_neg + (arr[( index ) as int] as i128) >= i128::MIN && sum_neg + (arr[( index ) as int] as i128) <= i128::MAX) by {
                let current_sum = sum_neg as int;
                let current_val = arr[( index ) as int] as int;
                assert(current_sum == sum_negative_to(arr@.subrange(0, index as int)));
                lemma_sum_negative_to_monotonic(arr@, (index as nat) + 1, ( arr.len() ) as nat);
                assert(sum_negative_to(arr@.subrange(0, index as int + 1)) <= i128::MAX as int);
                assert(sum_negative_to(arr@.subrange(0, index as int + 1)) >= i128::MIN as int);
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