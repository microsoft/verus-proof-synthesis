
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

// Proof function to show the sum of negative numbers is bounded
proof fn lemma_sum_bound(seq: Seq<i64>, idx: nat)
    requires
        idx <= seq.len(),
    ensures
        sum_negative_to(seq.subrange(0, idx as int)) <= seq.len() as int * i64::MIN as int,
{
    if idx == 0 {
        // Base case, sum of empty sequence is 0
    } else {
        let prv = idx - 1;
        lemma_sum_bound(seq, prv as nat);
        assert(sum_negative_to(seq.subrange(0, idx as int))
               <= sum_negative_to(seq.subrange(0, prv as int)) + if seq[prv] < 0 {
                    seq[prv] as int
                } else {
                    0 as int
               });
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
        if (arr[index] < 0) {
            // Add assertion to ensure no overflow/underflow
            assert(sum_neg + (arr[( index ) as int] as i128) >= i128::MIN && sum_neg + (arr[( index ) as int] as i128) <= i128::MAX) by {

                lemma_sum_bound(arr@, index as nat);
                // Additional safety checks can be added as necessary.
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