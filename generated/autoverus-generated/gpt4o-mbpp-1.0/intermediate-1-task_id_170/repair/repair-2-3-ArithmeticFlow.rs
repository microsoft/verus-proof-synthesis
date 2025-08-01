
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn sum_to(arr: Seq<i64>) -> int
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}

proof fn lemma_monotonic_sum(arr: Seq<i64>, start: int, end: int)
    requires
        0 <= start <= end < arr.len(),
    ensures
        forall |i: int|
            start <= i <= end ==> sum_to(arr.subrange(start, i)) <= sum_to(arr.subrange(start, end + 1))
{
    // Monotonic lemma to ensure sum_to is non-decreasing over the specified range.
    decreases end - start + 1;
    if start < end {
        lemma_monotonic_sum(arr, start, end - 1);
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
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
    {
        // Assertion to check for overflow
        assert(arr[index] as i128 >= 0 ==> sum + (arr[index] as i128) <= i128::MAX, "Overflow checking failed: Overflow would occur if we added arr[index] to sum");
        assert(arr[index] as i128 < 0 ==> sum + (arr[index] as i128) >= i128::MIN, "Overflow checking failed: Underflow would occur if we added arr[index] to sum");

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