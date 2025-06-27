
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
        sum_negative_to(seq.drop_last()) + if (seq.last() < 0) { seq.last() as int } else { 0 as int }
    }
}

proof fn lemma_sum_negative_to_monotonic(seq: Seq<i64>, n: nat)
    requires
        0 <= n <= seq.len(),
    ensures
        sum_negative_to(seq.subrange(0, ( n ) as int)) <= sum_negative_to(seq),
{
    if n < seq.len() {
        lemma_sum_negative_to_monotonic(seq, n + 1);
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
            sum_neg == sum_negative_to(arr@.subrange(0, index as int)) as i128,
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k], // ensures array `arr` is not modified in the loop
    {
        if arr[index] < 0 {
            // Insert assertion to ensure no arithmetic underflow/overflow occurs
            assert(sum_neg >= i128::MIN - arr[( index ) as int] as i128 && sum_neg <= i128::MAX - arr[( index ) as int] as i128) by {
                lemma_sum_negative_to_monotonic(arr@, ( index + 1 ) as nat);
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
// Safe: False