use vstd::prelude::*;

fn main() {}

verus! {

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
    
    let arr_len = arr.len(); // Preserve the length of the array for invariant
    
    while index < arr_len 
        invariant 
            0 <= index <= arr_len,
            sum_neg == sum_negative_to(arr@.take(index as int)),
            arr@.len() == arr_len,
    {
        if arr[index] < 0 {
            sum_neg = sum_neg + (arr[index] as i128);
        }
        index += 1;
    }
    sum_neg
}

} // verus!
// Score: (1, 3)
// Safe: False