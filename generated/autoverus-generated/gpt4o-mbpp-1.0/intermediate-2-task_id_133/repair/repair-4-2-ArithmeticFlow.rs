
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

// Lemma to prove the bounds of sum_negative_to for safety
proof fn lemma_sum_negative_bound(seq: Seq<i64>)
    ensures
        sum_negative_to(seq) >= (-(1 << 127)) && sum_negative_to(seq) <= (1 << 127) - 1,
    decreases seq.len()
{
    if seq.len() > 0 {
        lemma_sum_negative_bound(seq.drop_last());

        assert(seq.last() >= -(1 << 63) && seq.last() < (1 << 63));
        let last_val = if seq.last() < 0 { seq.last() as int } else { 0 };

        assert(sum_negative_to(seq.drop_last()) + last_val >= (-(1 << 127)));
        assert(sum_negative_to(seq.drop_last()) + last_val <= (1 << 127) - 1);
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
            sum_neg >= (-(1 << 127)) && sum_neg <= (1 << 127) - 1, // Added invariant for sum_neg bounds
    {
        if (arr[index] < 0) {
            // Assertion to prevent arithmetic underflow/overflow
            assert(sum_neg + (arr[( index ) as int] as i128) >= (-(1 << 127)) && sum_neg + (arr[index] as i128) <= (1 << 127) - 1) by {
                lemma_sum_negative_bound(arr@.subrange(0, index as int + 1));
                assert(sum_negative_to(arr@.subrange(0, index as int + 1)) >= (-(1 << 127)));
                assert(sum_negative_to(arr@.subrange(0, index as int + 1)) <= (1 << 127) - 1);
                assert(sum_neg + (arr[index] as i128) >= (-(1 << 127))); // Needed for verification
                assert(sum_neg + (arr[index] as i128) <= (1 << 127) - 1); // Needed for verification
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

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: True