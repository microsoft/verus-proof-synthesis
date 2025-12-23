
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

proof fn non_negative_seq(arr: Seq<i64>, start: nat, end: nat)
    requires
        0 <= start <= end < arr.len(),
    ensures
        forall |i: nat| start <= i <= end ==> 0 <= arr[( i ) as int] as int,
{
    // Additional lemma to assert that the elements are non-negative
    // if you require assumptions about elements, otherwise this could be omitted
}

proof fn lemma_sum_bounds(arr: Seq<i64>, start: nat, end: nat)
    requires
        0 <= start <= end < arr.len(),
    ensures
        sum_to(arr.subrange(start, end + 1)) <= 2_i128.pow(127) - 1,
{
    if start == end {
        assert(arr[start] as i128 <= 2_i128.pow(127) - 1);
    } else {
        lemma_sum_bounds(arr, start, end - 1);
        assert(sum_to(arr.subrange(start, end)) + arr[end] as i128 <= 2_i128.pow(127) - 1);
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
        // Add the assertion to check for overflow before addition
        assert(sum + arr[index] as i128 <= 2_i128.pow(127) - 1) by {
            lemma_sum_bounds(arr@, start as nat, end as nat);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!



//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: True