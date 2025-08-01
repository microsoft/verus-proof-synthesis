
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

proof fn lemma_sum_to_bound(arr: Seq<i64>, start: int, end: int, index: int)
    requires
        0 <= start <= end,
        start <= end < arr.len(),
        start <= index <= end,
    ensures
        sum_to(arr.subrange(start, index + 1)) + arr[index as int] < i128::MAX,
    decreases arr.len()
{
    // Assuming arr[index] as i128 won't overflow i128
    assert(arr[index as int] as int + (sum_to(arr.subrange(start, index + 1)) as i64) < i128::MAX as i64);
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
        // Assert the correctness of the bound
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX) by {
            lemma_sum_to_bound(arr@, start as int, end as int, index as int);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!





//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 5
// Safe: True