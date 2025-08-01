
use vstd::prelude::*;
fn main() {}

verus! {
    fn get_first_elements(arr: &Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() > 0,
        ensures
            arr.len() == result.len(),
            forall|i: int| 0 <= i < arr.len() ==> #[trigger] result[i] == #[trigger] arr[i][0],
    {
        let mut first_elem_arr: Vec<i32> = Vec::new();
        let mut index = 0;
        while index < arr.len()
            invariant
                first_elem_arr.len() == index,
                forall|i: int| 0 <= i < index ==> #[trigger] first_elem_arr[i] == #[trigger] arr[i][0],
                index <= arr.len(),
        {
            let seq = &arr[index];
            first_elem_arr.push(seq[0]);

            proof {
                // Proof block to maintain the loop invariants
                assert(first_elem_arr.len() == index + 1);
                assert(forall|i: int| 0 <= i < index + 1 ==> first_elem_arr[i] == arr[i][0]);
            }
            
            index += 1;
        }

        proof {
            // Final assertion to ensure the postconditions
            assert(arr.len() == first_elem_arr.len());
            assert(forall|i: int| 0 <= i < arr.len() ==> first_elem_arr[i] == arr[i][0]);
        }

        first_elem_arr
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpab05e2p1`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: True