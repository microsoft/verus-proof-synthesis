
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
    {
        // Assert that adding the next element won't cause overflow
        assert(i128::MAX - (arr[( index ) as int] as i128) >= sum); // Ensure no overflow
        
        // Corrected assertion to ensure no underflow by checking if sum minus the next element is greater than or equal to i128::MIN
        assert(sum - (arr[( index ) as int] as i128) >= i128::MIN); // Corrected assertion to ensure no underflow

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!




//         assert(i128::MIN - (arr[( index ) as int] as i128) <= sum); // Ensure no underflow
//   assertion failed: i128::MIN - (arr[( index ) as int] as i128) <= sum

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 5
// Safe: True