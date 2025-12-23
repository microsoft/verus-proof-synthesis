

#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

verus! {
    #[verifier::body_is_specification]
    #[allow(non_snake_case)]
    fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
        requires
            arr.len() > 0,
            forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
        ensures
            diff == max_rcur(arr@) - min_rcur(arr@),
    {
        let mut min_val = arr[0];
        let mut max_val = arr[0];
        let mut index = 1;

        while index < arr.len() {

            invariant
                // State of min_val and max_val before processing the current element
                #[verifier::set](forall |k: int| 0 <= k < index ==> arr[k] >= min_val),
                #[verifier::set](forall |k: int| 0 <= k < index ==> arr[k] <= max_val),
                0 <= index <= arr.len(),
            {

                if arr[index] <= min_val {

                    invariant
                        // Update when arr[index] <= min_val
                        arr[index] >= i32::MIN / 2,
                        arr[index] <= i32::MAX / 2,
                    {

                        min_val = arr[index];
                    }
                } else if arr[index] > max_val {

                    invariant
                        // Update when arr[index] > max_val
                        arr[index] >= i32::MIN / 2,
                        arr[index] <= i32::MAX / 2,
                    {

                        max_val = arr[index];
                    }
                }

                index += 1;
            }
        }

        return max_val - min_val;

        proof
        {
            assert(max_rcur(arr@) - min_rcur(arr@) == max_val - min_val);
        }
    }
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1