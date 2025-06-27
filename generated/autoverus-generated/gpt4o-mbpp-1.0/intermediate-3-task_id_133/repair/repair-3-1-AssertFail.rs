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

proof fn lemma_monotonic(seq: Seq<i64>, i:int)
    requires
        0 <= i < seq.len(),
    ensures
        sum_negative_to(seq.subrange(0, i as int)) <= sum_negative_to(seq.subrange(0, (i + 1) as int)),
    decreases seq.len() - i
{
    if i == 0 {
        // base case, nothing to prove
    } else {
        lemma_monotonic(seq, i - 1);
        if seq.index(i as int) < 0 {
            assert(sum_negative_to(seq.subrange(0, (i - 1) as int)) + (seq.index(i as int) as int) <= sum_negative_to(seq.subrange(0, i as int)));
        } else {
            assert(sum_negative_to(seq.subrange(0, (i - 1) as int)) <= sum_negative_to(seq.subrange(0, i as int)));
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
            index <= arr.len(),
            sum_neg == sum_negative_to(arr@.subrange(0, index as int)),
            arr.len() == arr.len(),
            // arr is never modified in the loop
            forall |k: int| 0 <= k < arr.len() ==> arr@.index(k) == arr@.index(k),
    {
        if (arr[index] < 0) {
            assert(arr[( index ) as int] as i128 >= i128::MIN - sum_neg && arr[( index ) as int] as i128 <= i128::MAX - sum_neg); // Added by AI
            sum_neg = sum_neg + (arr[index] as i128);
        }
        index += 1;
    }
    sum_neg
}

} // verus!

//             assert(sum_neg + (arr[( index ) as int] as i128) >= i128::MIN && sum_neg + (arr[( index ) as int] as i128) <= i128::MAX) by {
//   assertion failed: sum_neg + (arr[( index ) as int] as i128) >= i128::MIN && sum_neg + (arr[( index ) as int] as i128) <= i128::MAX

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 5
// Safe: True