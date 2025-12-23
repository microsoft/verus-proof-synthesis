
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

proof fn lemma_sum_to_monotonic(arr: Seq<i64>, n: nat)
    requires
        n <= arr.len(),
    ensures
        forall |i: nat| 0 <= i <= n ==> sum_to(arr.subrange(0, ( i ) as int)) <= sum_to(arr.subrange(0, ( n ) as int)),
{
    // Proof of monotonicity
    if n > 0 {
        lemma_sum_to_monotonic(arr, ( n - 1 ) as nat);
        assert(sum_to(arr.subrange(0, n - 1)) <= sum_to(arr.subrange(0, ( n ) as int)));
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
        assert(sum + arr[( index ) as int] as i128 <= sum_to(arr.subrange(start as int, _end as int))) by {
            lemma_sum_to_monotonic(arr@, (_end as int));
        };
        
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!







//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True