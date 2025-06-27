
use vstd::prelude::*;
fn main() {}
verus! {

// Recursive specification for sum of elements in an array
spec fn sum_to(arr: Seq<i64>) -> int
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}

// Lemma function that ensures the bound of sum_to for a valid subrange
proof fn lemma_sum_bound(arr: Seq<i64>, start: nat, end: nat)
    requires
        0 <= start <= end < arr.len(),
    ensures
        sum_to(arr.subrange(( start ) as int, end + 1 as int)) <= int::MAX
{
    let mut sum = 0;
    for i in start..=end {
        sum += arr[i];
        assert(sum <= int::MAX);
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
            index <= _end,
            start <= end < arr.len(),
            sum == sum_to(arr@.subrange(start as int, index as int)),
            arr.len() == arr.len(), // Loop invariant specifying the length of the array
            forall |k: int| 0 <= k < arr.len() ==> arr[k as int] == arr[k as int], // Adding this invariant since arr is never modified in the loop
            index < arr.len(), // Invariant about the array index not out of bound
    {
        // Ensure the addition will not cause overflow
        assert(sum + arr[index] as i128 <= int::MAX as i128) by {
            lemma_sum_bound(arr@, start as nat, end as nat);
        };

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}
} // verus!



//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 9
// Safe: True