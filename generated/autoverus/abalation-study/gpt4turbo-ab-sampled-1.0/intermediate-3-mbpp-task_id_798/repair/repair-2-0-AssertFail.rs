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
            i128::MIN <= sum, // Added invariant to ensure sum remains above MIN
            sum <= i128::MAX, // Added invariant to ensure sum does not exceed MAX
    {
        // Assert that adding the next element on the right-hand side won't cause overflow
        assert(i128::MAX - sum >= (arr[( index ) as int] as i128)); // Corrected overflow check
        // Assert that adding the next element on the left-hand side won't cause underflow
        assert(i128::MIN - sum <= (arr[( index ) as int] as i128)); // Corrected underflow check, but might not be necessary based on the corrected overflow check and invariants

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!





//         assert(i128::MIN - (arr[( index ) as int] as i128) <= sum); // Ensure no underflow
//   assertion failed: i128::MIN - (arr[( index ) as int] as i128) <= sum

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4
// Safe: True