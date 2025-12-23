
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
        proof {
            assert(first_elem_arr.len() == 0); // Initial length of first_elem_arr is 0
        }
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
                assert(first_elem_arr.len() == index as usize + 1); // The length invariant
                assert(index as int < arr.len()); // The loop bound invariant
                assert(forall|i: int| 0 <= i < index ==> #[trigger] first_elem_arr[i] == #[trigger] arr[i][0]); // Ensuring all previous elements match
            }
            index += 1;
        }
        first_elem_arr
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp26_wqysz`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False