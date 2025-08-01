
#[allow(unused_imports)]
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

proof fn lemma_sum_to_monotonic(arr: Seq<i64>, start: nat, end: nat, index: nat)
    requires
        0 <= start <= index <= end < arr.len(),
    ensures
        sum_to(arr.subrange(start as int, end as int)) >= sum_to(arr.subrange(start as int, index as int)),
    decreases end - index
{
    if start < end {
        lemma_sum_to_monotonic(arr, start, ( end - 1 ) as nat, index);
    }
}

fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)
    requires
        0 <= start <= end,
        end < arr.len(),
    ensures
        sum_to(arr@.subrange(start as int, end as int + 1)) == sum,
{
    let mut index = start;
    let mut sum = 0i128;
    let _end = end + 1;
    while index < _end
        invariant
            0 <= start <= end,
            end < arr.len(),
            0 <= index <= end + 1,
            sum == sum_to(arr@.subrange(start as int, index as int)),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr[k],
    {
        assert(sum + arr[( index ) as int] as i128 >= i128::MIN && sum + arr[( index ) as int] as i128 <= i128::MAX) by {
            lemma_sum_to_monotonic(arr@, start as nat, end as nat + 1, index as nat);
        };
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!





//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 8
// Safe: False