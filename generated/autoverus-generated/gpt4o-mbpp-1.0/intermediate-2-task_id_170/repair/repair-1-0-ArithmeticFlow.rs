
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

proof fn lemma_sum_to_monotonic(arr: Seq<i64>, start: int, end: int, index: int)
    requires
        0 <= start <= end < arr.len(),
        start <= index <= end,
    ensures
        sum_to(arr.subrange(start, end + 1)) >= sum_to(arr.subrange(start, index + 1)),
{
    if start <= index < end {
        lemma_sum_to_monotonic(arr, start, end, index + 1);
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
            0 <= start <= end < arr.len(),
            _end == end + 1,
            start <= index <= _end,
            sum_to(arr@.subrange(start as int, index as int)) == sum,
            forall |k: int| 0 <= k < arr.len() ==> arr@.index(k) == arr@[k], // Added invariant to cover every element in the array
    {
        assert(sum + arr[( index ) as int] as i128 <= sum_to(arr@.subrange(start as int, end as int + 1))) by {
            lemma_sum_to_monotonic(arr@, start as int, end as int, index as int);
        };
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!



//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True