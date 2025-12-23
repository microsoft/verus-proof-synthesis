

use vstd::prelude::*;

fn main() {}

verus! {

spec fn sum_to(arr: Seq<i64>) -> i128
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last() as i128
    }
}

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum == sum_to(arr@),
{
    let mut index: usize = 0;
    let mut sum: i128 = 0;

    % This loop invariant ensures that the partial sum up to the current index
    % is equal to the sum_to of the subarray up to that index.
    while (index < arr.len())
        invariant
            index <= arr.len(),
            sum_to(arr@.subrange(0, index as int)) == sum,
            arr.len() == old(arr.len()),
    {
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1