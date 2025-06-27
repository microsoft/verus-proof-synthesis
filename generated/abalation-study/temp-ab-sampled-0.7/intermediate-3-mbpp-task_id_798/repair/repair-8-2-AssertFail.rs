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
            forall |k:int| 0 <= k < arr.len() ==> arr[k] == arr[k], // Invariant for covering all elements in the array
            arr.len() == arr.len(), // Loop invariant specifying the length of the array
            sum <= i128::MAX,
            sum >= i128::MIN,
            forall |k: int| 0 <= k < index ==> sum + arr[k] as i128 <= i128::MAX && sum + arr[k] as i128 >= i128::MIN, // Added by AI, for assertion fail
            index < arr.len() ==> sum + arr[( index ) as int] as i128 <= i128::MAX && sum + arr[( index ) as int] as i128 >= i128::MIN // New invariant to ensure the assertion holds
    {
        // Assertion to check for overflow/underflow
        assert(sum + arr[(index) as int] as i128 <= i128::MAX && sum + arr[(index) as int] as i128 >= i128::MIN);

        sum = sum + arr[index] as i128;
        index += 1;
    }
    sum
}

}



//         assert(sum + arr[(index) as int] as i128 <= i128::MAX && sum + arr[(index) as int] as i128 >= i128::MIN);
//   assertion failed: sum + arr[(index) as int] as i128 <= i128::MAX && sum + arr[(index) as int] as i128 >= i128::MIN

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4
// Safe: True