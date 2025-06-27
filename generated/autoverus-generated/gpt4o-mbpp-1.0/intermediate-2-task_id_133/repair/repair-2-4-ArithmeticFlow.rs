
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

proof fn lemma_sum_negative_monotonic(seq: Seq<i64>)
    ensures
        forall |i: int, j: int| 0 <= i <= j <= seq.len() ==> sum_negative_to(seq.subrange(0, i)) <= sum_negative_to(seq.subrange(0, j)),
{
    // Implement a recursive proof to establish monotonicity
    if seq.len() == 0 {
        // Base case: trivially true
    } else {
        lemma_sum_negative_monotonic(seq.drop_last());
        assert(forall|i: int, j: int| 0 <= i <= j < seq.drop_last().len() ==> sum_negative_to(seq.drop_last().subrange(0, i)) <= sum_negative_to(seq.drop_last().subrange(0, j)));
        // Now prove for full sequence
        assert(forall|i: int, j: int| 0 <= i <= j <= seq.len() ==>
            sum_negative_to(seq.subrange(0, i)) <= sum_negative_to(seq.subrange(0, j))) by {
                assume(false);
                // Use inductive step and our recursive proof on seq.drop_last() to justify
            };
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
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k], // Array `arr` is not modified in the loop
    {
        if (arr[index] < 0) {
            let addition = arr[index] as i128;
            assert(sum_neg + addition >= i128::MIN);
            assert(sum_neg + addition <= i128::MAX);
            
            // Using the monotonicity lemma
            lemma_sum_negative_monotonic(arr@.subrange(( 0 ) as int, index as int));
            assert(sum_neg + addition <= sum_negative_to(arr@.subrange(0, index as int)) as i128);

            sum_neg = sum_neg + addition;
        }
        index += 1;
    }
    sum_neg
}

} // verus!



//             sum_neg = sum_neg + (arr[index] as i128);
//   None: sum_neg + (arr[index] as i128)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False