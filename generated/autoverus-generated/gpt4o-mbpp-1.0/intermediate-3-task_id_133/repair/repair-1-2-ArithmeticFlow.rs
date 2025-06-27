
#[allow(unused_imports)]
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
            assert({
                let new_sum = sum_neg + (arr[index] as i128);
                i128::MIN <= new_sum && new_sum <= i128::MAX
            });
            sum_neg = sum_neg + (arr[index] as i128);
        }
        index += 1;
    }
    sum_neg
}

} // verus!

By adding the assertion:
rust
assert({
    let new_sum = sum_neg + (arr[index] as i128);
    i128::MIN <= new_sum && new_sum <= i128::MAX
});

before the line:
rust
sum_neg = sum_neg + (arr[index] as i128);


//             sum_neg = sum_neg + (arr[index] as i128);
//   None: sum_neg + (arr[index] as i128)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False