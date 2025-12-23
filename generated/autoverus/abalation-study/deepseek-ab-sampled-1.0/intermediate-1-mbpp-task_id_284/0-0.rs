
use vstd::prelude::*;

fn main() {}

verus! {

fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)),
    ( requires ) as bool
        // Any necessary preconditions can be specified here
    {
        let mut index = 0;

        while (index < arr.len())
            invariant
                index <= arr.len(),
                0 <= index < arr.len() ==> arr[index] == element,
        {
            if arr[index] != element {
                return false;
            }
            index += 1;
        }

        true
    }

} // verus!


// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3