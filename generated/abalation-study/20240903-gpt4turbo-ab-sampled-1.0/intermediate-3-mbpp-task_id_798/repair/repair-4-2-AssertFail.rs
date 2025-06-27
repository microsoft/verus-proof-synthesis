
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

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;
    while index < arr.len()
        invariant
            index <= arr.len(),
            sum == sum_to(arr@.subrange(0, index as int)) as i128,
            arr.len() == arr@.len(),
            i128::MIN <= sum, // Ensure the invariant maintains no underflow
            i128::MAX >= sum, // Ensure the invariant maintains no overflow
            i128::MAX - (arr@.subrange(index as int, arr.len() as int).map_values(|x: (int, i64)| x.1 as FnSpec<(i64,), _>).fold(0i128, |acc, x| acc + x)) >= sum, // Ensure no overflow for future additions
            i128::MIN + (arr@.subrange(index as int, arr.len() as int).map_values(|x: (int, i64)| x.1 as i128).fold(0i128, |acc, x| acc + x)) <= sum, // Ensure no underflow for future subtractions
    {
        // Assert that adding the next element won't cause overflow
        assert(i128::MAX - (arr[index] as i128) >= sum); // Ensure no overflow
        assert(i128::MIN - (arr[index] as i128) <= sum); // Ensure no underflow

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!



//         assert(i128::MIN - (arr[( index ) as int] as i128) <= sum); // Ensure no underflow
//   assertion failed: i128::MIN - (arr[( index ) as int] as i128) <= sum

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False