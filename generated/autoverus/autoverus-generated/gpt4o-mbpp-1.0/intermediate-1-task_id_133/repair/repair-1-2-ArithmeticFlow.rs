
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

spec fn is_within_i128_range(value: int) -> bool {
    value >= (i128::MIN as int) && value <= (i128::MAX as int)
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
    {
        if arr[index] < 0 {
            let new_sum_neg = sum_neg + (arr[index] as i128);
            assert(is_within_i128_range(sum_negative_to(arr@.subrange(0, index as int)) + (arr[( index ) as int] as int)));
            assert!(new_sum_neg >= i128::MIN && new_sum_neg <= i128::MAX);
            sum_neg = new_sum_neg;
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