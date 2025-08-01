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
    {
        // Ensure that conversion to i128 does not overflow or underflow
        let next_val_i128  = arr[index] as i128;

        // Assert that adding the next element won't cause overflow
        assert(i128::MAX - sum >= next_val_i128); // Ensure no overflow

        // For underflow, note that since `i128::MIN` is negative,
        // subtracting a negative `next_val_i128` (when original i64 value is negative) 
        // can potentially cause underflow.
        // To ensure there is no underflow when adding a negative, 
        // check that `sum` itself must be greater than the absolute value of `i128::MIN` plus `next_val_i128`.
        assert(sum - i128::MIN >= -next_val_i128); // Ensure no underflow corrected
        
        sum = sum + next_val_i128;
        index += 1;
    }
    sum
}

} // verus!

//         assert(sum - i128::MIN >= -(arr[( index ) as int] as i128)); // Ensure no underflow corrected
//   assertion failed: sum - i128::MIN >= -(arr[( index ) as int] as i128)

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4
// Safe: False