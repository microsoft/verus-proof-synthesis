
use vstd::prelude::*;
fn main() {}
verus! {

spec fn sum_to(arr: Seq<i64>) -> int
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}

fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)
    requires
        0 <= start <= end,
        start <= end < arr.len(),
    ensures
        sum_to(arr@.subrange(start as int, end + 1 as int)) == sum,
{
    let mut index = start;
    let mut sum = 0i128;
    let _end = end + 1;
    while index < _end
        invariant
            0 <= start <= end,
            start <= end < arr.len(),
            arr.len() == arr.len(),
            0 <= start,
            start <= end,
            _end == end + 1,
            index <= _end,
            start <= index <= end + 1,
            sum == sum_to(arr@.subrange(start as int, index as int)),
            // Added invariant to cover every element in arr, as arr is never modified in the loop
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
    {
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!
