
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
            0 <= index < arr.len(), // The array arr is never modified in the loop
            sum + arr[index] as i128 >= sum, // Bound assertion added here to prevent overflow
    {
        assert(sum + arr[index] as i128 >= sum, "Sum out of bounds");

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