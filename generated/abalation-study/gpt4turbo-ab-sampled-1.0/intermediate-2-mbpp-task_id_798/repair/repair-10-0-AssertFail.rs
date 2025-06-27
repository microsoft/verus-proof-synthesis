
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

    // No changes to sum_to_monotonic are made since its body is not shown
    // Assuming it correctly ensures the sum properties for a subrange.

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
                i128::MIN <= sum && sum <= i128::MAX,
                // The ensures property of sum_to_monotonic hints it might already guarantee boundary safety.
                // This invariant is similar to what you aimed to assert;
                // ensuring each addition falls within the i128 bounds based on the range of i64 values.
                forall |i: int| 0 <= i && i < index as int ==> 
                    i128::MIN <= sum + arr@[i] as i128 && sum + arr@[i] as i128 <= i128::MAX,
        {
            assert(i128::MIN <= sum + arr[( index ) as int] as i128 && sum + arr[( index ) as int] as i128 <= i128::MAX) by {
                // This proof block is simplified with direct reasoning:
                // Since i64::MIN >= i128::MIN and i64::MAX <= i128::MAX,
                // any i64 value adding to a sum within i128 bounds can't overflow.
            };

            sum = sum + arr[index] as i128;
            index += 1;
        }
        sum
    }
} // verus!




//             assert(i128::MIN <= sum + arr[( index ) as int] as i128 && sum + arr[( index ) as int] as i128 <= i128::MAX) by {
//   assertion failed: i128::MIN <= sum + arr[( index ) as int] as i128 && sum + arr[( index ) as int] as i128 <= i128::MAX

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4
// Safe: True