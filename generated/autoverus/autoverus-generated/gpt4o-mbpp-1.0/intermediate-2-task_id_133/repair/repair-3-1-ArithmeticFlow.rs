
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

proof fn lemma_bound_sum_negative(seq: Seq<i64>, index: nat)
    requires
        index <= seq.len(),
    ensures
        let sum_neg = sum_negative_to(seq.subrange(0, index)) as i128 in
        forall |i: nat| 0 <= i < index ==> seq[i] as i128 >= -((1 << 127) - sum_neg) && seq[i] as i128 <= (1 << 127) - 1
{
    if index == 0 {
        return;
    } else {
        let last_elem = seq.index(index - 1);
        assert(seq.subrange(0, index).drop_last() == seq.subrange(0, index - 1));

        lemma_bound_sum_negative(seq, index - 1);
        assert(sum_negative_to(seq) == sum_negative_to(seq.subrange(0, index - 1))
            + if last_elem < 0 {
                last_elem as int
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
            index <= arr.len(), // copied invariant
            sum_neg == sum_negative_to(arr@.subrange(0, index as int)) as i128,
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k], // added this invariant because array `arr` is not modified in the loop
    {
        if (arr[index] < 0) {
            assert({
                let arr_elem = arr[index] as i128;
                sum_neg >= i128::MIN + arr_elem && sum_neg <= i128::MAX + arr_elem
            }) by {
                lemma_bound_sum_negative(arr@, index as nat);
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