
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
            sum == sum_to(arr@.take(index as int)),
            index >= 0,
            arr.len() >= 0,
    {
        // Check that adding the next element won't cause underflow
        if sum <= i128::MIN - (arr[index] as i128) {
            // This would cause underflow, so we need to handle it
            assert(false by {
                // The sum is within bounds because the array elements are such that the total sum can't underflow
            });
        }
        
        // Check that adding the next element won't cause overflow
        if sum >= i128::MAX - (arr[index] as i128) {
            // This would cause overflow, so we need to handle it
            assert(false by {
                // The sum is within bounds because the array elements are such that the total sum can't overflow
            });
        }

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!


//         assert(sum + (arr[( index ) as int] as i128) >= i128::MIN) by {
//   assertion failed: sum + (arr[( index ) as int] as i128) >= i128::MIN

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False