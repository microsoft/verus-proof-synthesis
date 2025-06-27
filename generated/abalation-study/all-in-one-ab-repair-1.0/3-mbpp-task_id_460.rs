
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::spinoff_prover]
    fn get_first_elements(arr: &Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            forall|i: int| 0 <= i < arr.len() ==> # [trigger] arr[i].len() > 0,
        ensures
            arr.len() == result.len(),
            forall|i: int| 0 <= i < arr.len() ==> result[i] == arr[i][0],
    {
        let mut first_elem_arr: Vec<i32> = Vec::new();
        let mut index = 0;
        while index < arr.len()
            invariant
                first_elem_arr@.len() == index,
                index <= arr.len(),
                forall|i: int|
                    0 <= i < index ==> first_elem_arr@[i] == arr@[i][0],
                forall|i: int| 0 <= i < arr.len() ==> arr[i].len() > 0,
        {
            let seq = &arr[index];
            first_elem_arr.push(seq[0]);
            index += 1;
        }
        first_elem_arr
    }
}

// Score: (2, 0)
// Safe: False