
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
            sum_to(arr.drop_last()) + arr.last() as int
        }
    }

    proof fn sum_to_monotonic(arr: Seq<i64>, index: nat)
        requires
            arr.len() > 0, // ensures array is not empty
            index < arr.len(),
        ensures
            i128::MIN <= sum_to(arr.subrange(0, ( index + 1 ) as int)) as i128,
            sum_to(arr.subrange(0, ( index + 1 ) as int)) as i128 <= i128::MAX,
    {
        if arr.len() == 1 {
            assert(arr[0] as int >= i64::MIN as int);
            assert(arr[0] as int <= i64::MAX as int);
        } else if index > 0 {
            sum_to_monotonic(arr, ( index - 1 ) as nat);
        }
        // Directly stating the property can help in understanding the
        // bounds but may not always be necessary or sufficient for a proof.
        // More detailed invariants or lemmas might be required depending on 
        // the complexity of the `sum_to` function and the sequences it operates on.
    }

    fn sum(arr: &Vec<i64>) -> (sum: i128)
        ensures
            sum_to(arr@) as i128 == sum,
    {
        let mut index = 0;
        let mut sum = 0i128;
        while index < arr.len()
            invariant
                index <= arr.len(),
                sum == sum_to(arr@.subrange(0, index as int)) as i128,
                arr.len() == arr@.len(),
                i128::MIN <= sum && sum <= i128::MAX,
                forall |i: int| 0 <= i && i < index as int ==> 
                    i128::MIN <= sum + arr@[i] as i128 && sum + arr@[i] as i128 <= i128::MAX,
        {
            assert(i128::MIN <= sum + arr[index as int] as i128 && sum + arr[index as int] as i128 <= i128::MAX) by {
                sum_to_monotonic(arr@, index as nat);
            };

            sum = sum + arr[index] as i128;
            index += 1;
        }
        sum
    }
} // verus!





//             assert(i128::MIN <= sum + arr[( index ) as int] as i128 && sum + arr[( index ) as int] as i128 <= i128::MAX) by {
//   assertion failed: i128::MIN <= sum + arr[( index ) as int] as i128 && sum + arr[( index ) as int] as i128 <= i128::MAX

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False