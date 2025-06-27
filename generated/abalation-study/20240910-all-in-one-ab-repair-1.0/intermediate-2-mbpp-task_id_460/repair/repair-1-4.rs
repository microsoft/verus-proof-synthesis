
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
                arr.len() == arr.len(),  // Invariant for arr length (constant)
                forall|i: int| 0 <= i < index ==> #[trigger] first_elem_arr[i] == #[trigger] arr[i][0],
                index <= arr.len(), // Ensure the loop index is within bounds
        {
            first_elem_arr.push(arr[index][0]);
            index += 1;
        }
        first_elem_arr
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp9ibz4pq9`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: False