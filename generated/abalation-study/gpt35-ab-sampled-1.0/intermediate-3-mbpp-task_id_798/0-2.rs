
use vstd::prelude::*;

fn main() {}

verus! {

spec proof fn lemma_sum_to_last<T>(arr: Seq<T>) -> int
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        lemma_sum_to_last(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;

    while index < arr.len()
        invariant
            index <= arr.len(),
            sum == lemma_sum_to_last(arr.subrange(0, index as int)),
    {
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1