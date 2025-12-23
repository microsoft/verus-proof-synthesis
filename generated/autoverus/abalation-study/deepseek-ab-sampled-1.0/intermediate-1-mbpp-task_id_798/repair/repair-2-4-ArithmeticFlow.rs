
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
        assert(sum + (arr[( index ) as int] as i128) <= i128::MAX) by {
            // The proof obligation is handled by ensuring that the next sum is within bounds.
        };
        assert(sum + (arr[( index ) as int] as i128) >= i128::MIN) by {
            // Similarly, ensure the sum does not underflow.
        };
        
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!




//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4
// Safe: True