
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

proof fn lemma_sum_negative_to_bounds(seq: Seq<i64>)
    requires
        // No specific requirements
    ensures
        sum_negative_to(seq) <= 0,
{
    if seq.len() != 0 {
        let last = seq.last() as int;
        lemma_sum_negative_to_bounds(seq.drop_last());
        if last < 0 {
            assert(sum_negative_to(seq) <= sum_negative_to(seq.drop_last()));
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
            sum_neg == sum_negative_to(arr@.subrange(0, index as int)) as i128,
            index < arr.len(), // Upper bound copied from the function pre-condition
            arr.len() == arr.len(), // Loop invariant specifying the length of the array
            sum_neg <= 0, // Since we only sum negative numbers
    {
        if (arr[index] < 0) {
            
            assert(sum_neg + (arr[( index ) as int] as i128) <= 0) by {
                lemma_sum_negative_to_bounds(arr@.subrange(0, index as int));
                if arr[( index ) as int] < 0 {
                    assert(arr[( index ) as int] as int <= 0); // Since arr[index] is negative
                    assert(sum_neg + (arr[( index ) as int] as i128) <= sum_neg); 
                }
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