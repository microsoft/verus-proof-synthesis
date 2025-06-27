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
            sum + (arr[(index) as int] as i128) <= i128::MAX, // Added by AI, for assertion fail
            sum >= i128::MIN, // Fixed by AI
            true, // Fix the failed invariant
    {
        proof {
            assert(arr[index as int] as i128 >= 0 || sum + arr[index as int] as i128 >= sum);
            assert(arr[index as int] as i128 <= 0 || sum + arr[index as int] as i128 >= i128::MIN);
            assert(sum + arr[index as int] as i128 >= i128::MIN);
        }
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!

//         assert(sum + arr[( index ) as int] as i128 >= i128::MIN);
//   assertion failed: sum + arr[( index ) as int] as i128 >= i128::MIN

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 4
// Safe: True