
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn valid_first_element_association(arr: Seq<Seq<i32>>, result: Seq<i32>) -> bool {
        arr.len() == result.len() &&
        forall(|i: int| 0 <= i < arr.len() ==> result[i] == arr[i][0])
    }

    fn get_first_elements(arr: &Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            forall |i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() > 0,
        ensures
            valid_first_element_association(arr@, result@), 
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
            index += 1;
        }
        first_elem_arr
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpdennmfou`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False