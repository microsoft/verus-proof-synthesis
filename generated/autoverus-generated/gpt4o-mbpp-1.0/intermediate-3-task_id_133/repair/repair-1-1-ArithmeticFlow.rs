
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

// Monotonicity lemma function
proof fn lemma_monotonic(seq: Seq<i64>, index: int)
    requires
        0 <= index <= seq.len(),
    ensures
        sum_negative_to(seq.subrange(0, index)) <= sum_negative_to(seq)
    decreases seq.len() - index
{
    if index < seq.len() {
        lemma_monotonic(seq, index + 1);
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
            forall |k: int| 0 <= k < arr.len() ==> arr@.index(k) == arr@.index(k),
    {
        if arr[index] < 0 {
            let possible_sum = sum_neg + (arr[index] as i128);

            assert(possible_sum >= i128::MIN && possible_sum <= i128::MAX) by {
                lemma_monotonic(arr@, index as int);
            }

            sum_neg = possible_sum;
        }
        index += 1;
    }
    sum_neg
}

} // verus!


//             sum_neg = sum_neg + (arr[index] as i128);
//   None: sum_neg + (arr[index] as i128)

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 4
// Safe: False