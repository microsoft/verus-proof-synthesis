
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

proof fn lemma_monotonic_sum_neg(seq1: Seq<i64>, seq2: Seq<i64>)
    requires
        seq1.len() <= seq2.len(),
        seq1 =~= seq2.subrange(0, ( seq1.len() ) as int),
    ensures
        sum_negative_to(seq1) <= sum_negative_to(seq2),
    decreases seq2.len()
{
    if seq1.len() < seq2.len() {
        lemma_monotonic_sum_neg(seq1, seq2.drop_last());
        if seq2.last() < 0 {
            assert(sum_negative_to(seq1) + seq2.last() as int <= sum_negative_to(seq2));
        } else {
            assert(sum_negative_to(seq1) <= sum_negative_to(seq2));
        }
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
            index <= arr.len(),
            sum_neg == sum_negative_to(arr@.subrange(0, index as int)) as i128,
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
    {
        if arr[index] < 0 {
            // Assertion about the bound of sum_neg + (arr[index] as i128)
            assert({
                let next_sum_neg = sum_neg + (arr[( index ) as int] as i128);
                next_sum_neg >= i128::MIN && next_sum_neg <= i128::MAX
            }) by {
                lemma_monotonic_sum_neg(arr@.subrange(0, index as int), arr@);
                assert(sum_negative_to(arr@.subrange(0, index as int)) <= sum_negative_to(arr@));
                assert(sum_neg <= sum_negative_to(arr@) as i128);
                assert((arr[( index ) as int] as i128) >= i64::MIN as i128 && (arr[( index ) as int] as i128) <= i64::MAX as i128); // Cast is safe
                assert(sum_neg + (arr[( index ) as int] as i128) <= i128::MAX);
                assert(sum_neg + (arr[( index ) as int] as i128) >= i128::MIN);
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

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 5
// Safe: False