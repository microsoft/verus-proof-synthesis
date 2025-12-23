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
            arr.len() == arr@.len(), // loop invariant for the "arr" length
            i128::MIN <= sum && sum <= i128::MAX, // Ensure sum is always within i128 bounds
    {
        // Assert to ensure sum stays within i128 bounds before addition
        assert(i128::MIN - arr[( index ) as int] as i128 <= sum && sum <= i128::MAX - arr[( index ) as int] as i128);

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!




//         assert(i128::MIN - arr[( index ) as int] as i128 <= sum && sum <= i128::MAX - arr[( index ) as int] as i128);
//   assertion failed: i128::MIN - arr[( index ) as int] as i128 <= sum && sum <= i128::MAX - arr[( index ) as int] as i128

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3
// Safe: True