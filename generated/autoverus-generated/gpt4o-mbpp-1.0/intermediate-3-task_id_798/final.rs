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
            arr@.len() == arr.len(),
            index <= arr.len(),
            sum == sum_to(arr@.subrange(0, (index) as int)),
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == arr@[k], // The array arr is never changed in the loop
            sum <= i128::MAX, // Ensure sum is within the bounds of i128
            sum >= i128::MIN, // Ensure sum is within the bounds of i128
            index < arr.len() ==> arr[( index ) as int] as i128 <= (i128::MAX - sum), // Ensure no overflow
            index < arr.len() ==> index >= 0, // Corrected by AI
    {
        // Ensure that the addition won't overflow
        assert(sum + arr[( index ) as int] as i128 <= i128::MAX);
        assert(sum + arr[( index ) as int] as i128 >= i128::MIN);
        
        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

} // verus!
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4