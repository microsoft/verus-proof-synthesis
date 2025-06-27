
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

proof fn lemma_sum_to_bounds(arr: Seq<i64>, start: int, end: int)
    requires
        0 <= start <= end < arr.len(),
        // Assuming elements of arr are in the range of i64
        forall |k: int| 0 <= k < arr.len() ==> arr[k] >= -(1<<63) && arr[k] < (1<<63),
    ensures
        sum_to(arr.subrange(start, end + 1)) >= -(1<<127) && sum_to(arr.subrange(start, end + 1)) < (1<<127),
    decreases end - start + 1
{
    if end == start {
        assert(arr[start] as int >= -(1<<127));
        assert(arr[start] as int < (1<<127));
    } else {
        lemma_sum_to_bounds(arr, start, end - 1);
        assert(sum_to(arr.subrange(start, end)) >= -(1<<127) && sum_to(arr.subrange(start, end)) < (1<<127));
        assert(arr[end] as int >= -(1<<127));
        assert(arr[end] as int < (1<<127));
    }
}

fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)
    requires
        0 <= start <= end,
        start <= end < arr.len(),
        // Bound check for individual elements
        forall |k: usize| 0 <= k < arr.len() ==> arr[k] >= -(1<<63) && arr[k] < (1<<63),
    ensures
        sum_to(arr@.subrange(start as int, end + 1 as int)) == sum,
{
    let mut index = start;
    let mut sum = 0i128;
    let _end = end + 1;

    // lemma invocation for the bound check
    lemma_sum_to_bounds(arr@, start as int, end as int);

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
            // Ensure elements in arr are constant as arr is never modified in the loop
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
    {
        // Adding assertion to check no overflow/underflow occurs when sum + arr[index] is computed
        assert(sum + arr[index] as i128 >= -(1<<127) && sum + arr[index] as i128 < (1<<127));

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False