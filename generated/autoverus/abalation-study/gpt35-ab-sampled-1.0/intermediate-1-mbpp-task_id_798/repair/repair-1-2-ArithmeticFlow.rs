
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
                // The array arr is not modified within the loop, as there is no x.set() operation.
                // Hence, we can use the following invariant to cover every element in the array.
                forall |k:int| 0 <= k < arr.len() ==> sum_to(arr@.subrange(0, k as int)) == sum_to(arr@.subrange(0, index as int)),
        {
            assert(
                sum + arr[( index ) as int] as i128 >= std::i64::MIN as i128 
                && sum + arr[( index ) as int] as i128 <= std::i64::MAX as i128
            );
            sum = sum + arr[index] as i128;
            index += 1;
        }
        sum
    }
}




//         sum = sum + arr[index] as i128;
//   None: sum + arr[index] as i128

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True