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
            i128::MIN <= sum + i64::MIN as i128, // Adjusted to ensure no underflow with addition
            i128::MAX >= sum + i64::MAX as i128, // Adjusted to ensure no overflow with addition
    {
        // Assert that adding the next element won't cause overflow
        assert(i128::MAX - sum >= (arr[( index ) as int] as i128)); // Ensure no overflow
        assert(sum - i128::MIN >= -(arr[( index ) as int] as i128)); // Ensure no underflow corrected

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!
// Score: (1, 3)
// Safe: True