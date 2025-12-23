
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
            proof {
                assert(seq.len() > 0); // Ensure each seq (Vec<i32>) has at least one element
            }
            first_elem_arr.push(seq[0]);
            index += 1;
        }
        first_elem_arr
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpg1szrk7_`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: True