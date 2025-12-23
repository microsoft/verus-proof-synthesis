
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

    proof fn lemma_index_bound(arr: Seq<i64>, index: int)
        requires
            0 <= index < arr.len(),
        ensures
            (sum_to(arr.take(index)) + arr[index]) as i128 <= i128::MAX,
        decreases index
    {
        // You can add your proof here
        // For example, if the elements of arr are non-negative, then the sum_to(arr.take(index)) + arr[index] is less than i128::MAX
    }

    fn sum(arr: &Vec<i64>) -> (sum: i128)
        ensures
            sum_to(arr@) == sum,
    {
        let mut index = 0;
        let mut sum = 0i128;
        while index < arr.len()
            invariant
                index <= arr.len() /* The length of arr does not change during this loop */,
                // forall |k:int| 0<= k < arr.len() ==> true /* The array elements are never modified in this loop */,
                (sum as i128 + arr[( index ) as int] as i128) >= i128::MIN,
                (sum as i128 + arr[( index ) as int] as i128) <= i128::MAX,
                (sum as i128) <= i128::MAX,
        {
            sum = sum + arr[index] as i128;
            index += 1;
        }
        sum
    }
} // verus!

// Score: (2, 3)
// Safe: True