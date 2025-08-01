
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

// Define the maximum and minimum bounds for i128 explicitly
const MAX_I128: i128 = i128::MAX;
const MIN_I128: i128 = i128::MIN;

fn sum(arr: &Vec<i64>) -> (sum: i128)
    ensures
        sum_to(arr@) == sum,
{
    let mut index = 0;
    let mut sum = 0i128;
    while index < arr.len()
        invariant
            arr@.len() == arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.subrange(0, (index) as int)),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr@[k], // The array arr is never changed in the loop,
            sum >= MIN_I128 && sum <= MAX_I128,  // Added to ensure sum's invariant is within i128 bounds
    {
        // Adding assertions to prevent overflow/underflow
        let tmp_sum = sum + arr[index] as i128;
        assert(tmp_sum <= MAX_I128);
        assert(tmp_sum >= MIN_I128);

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!


//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 4
// Safe: False