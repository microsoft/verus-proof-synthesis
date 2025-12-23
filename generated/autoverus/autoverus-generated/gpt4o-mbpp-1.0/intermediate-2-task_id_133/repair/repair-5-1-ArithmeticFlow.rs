
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

proof fn lemma_sum_bound(seq: Seq<i64>, idx: int, acc: int)
    requires
        0 <= idx < seq.len(),
        acc == sum_negative_to(seq.subrange(0, idx)),
    ensures
        sum_negative_to(seq.subrange(0, idx + 1)) + if seq[idx] < 0 { seq[idx] as int } else { 0 } == acc + (seq[idx] as int)
{
    if seq[idx] < 0 {
        assert(sum_negative_to(seq.subrange(0, idx + 1)) == sum_negative_to(seq.subrange(0, idx)) + seq[idx] as int);
    } else {
        assert(sum_negative_to(seq.subrange(0, idx + 1)) == sum_negative_to(seq.subrange(0, idx)));
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
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k], // array `arr` is not modified in the loop
    {
        if arr[index] < 0 {
            assert({
                let new_sum_neg = sum_neg + (arr[( index ) as int] as i128);
                (new_sum_neg >= i128::MIN) && (new_sum_neg <= i128::MAX)
            });
            sum_neg = sum_neg + (arr[index] as i128);
        }
        index += 1;
    }
    sum_neg
}

}



//             sum_neg = sum_neg + (arr[index] as i128);
//   None: sum_neg + (arr[index] as i128)

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 6
// Safe: False