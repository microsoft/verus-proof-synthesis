
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

// Lemma to show sum_negative_to is monotonic with respect to its sequence argument
proof fn lemma_monotonic_sum_negative_to(seq: Seq<i64>, new_elem: i64)
    requires seq.len() > 0,
    ensures seq.last() < 0 ==> sum_negative_to(seq.push(new_elem)) <= sum_negative_to(seq) + new_elem as int,
{
    assert(seq.len() > 0);
    assert(seq.last() < 0);
    let new_sum = if new_elem < 0 {
        new_elem as int
    } else {
        0 as int
    };
    assert(sum_negative_to(seq.push(new_elem)) == sum_negative_to(seq) + new_sum);
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
        if arr[index] < 0 {
            let next_sum_neg = sum_neg + (arr[index] as i128);
            assert(next_sum_neg >= i128::MIN && next_sum_neg <= i128::MAX) by {
                lemma_monotonic_sum_negative_to(arr@.subrange(0, index as int), arr[( index ) as int]);
            };
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