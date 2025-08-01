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
        end < arr.len(),
    ensures
        sum_to(arr@.subrange(start as int, end + 1 as int)) == sum,
{
    let mut index = start;
    let mut sum = 0i128;
    let _end = end + 1;

    while index < _end
    invariant
        start <= index <= _end,
        sum == sum_to(arr@.subrange(start as int, index as int)),
        _end == end + 1,
        end < arr.len(),
    {

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!
// Score: (2, 2)
// Safe: False