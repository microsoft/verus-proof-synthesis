
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn get_first_elements(arr: &Vec<Vec<i32>>) -> (result: Vec<i32>)
    requires
        forall|i: int| 0 <= i < arr.len() ==> # [trigger] arr[i].len() > 0,
    ensures
        arr.len() == result.len(),
        forall|i: int| 0 <= i < arr.len() ==> # [trigger] result[i] == # [trigger] arr[i][0],
{
    let mut first_elem_arr: Vec<i32> = Vec::new();
    let mut index = 0;
    while index < arr.len()
        invariant
            first_elem_arr.len() == index,
            forall|i: int|
                0 <= i < index ==> # [trigger] first_elem_arr[i] == # [trigger] arr[i][0],
            forall|i: int| 0 <= i < index ==> first_elem_arr[i] == arr[i][0],
            forall|j: int|
                0 <= j < index ==> # [trigger] first_elem_arr[j] == # [trigger] arr[j][0],
            index <= arr.len(),
            forall|i: int| 0 <= i < arr.len() ==> # [trigger] arr[i].len() > 0,
            arr.len() == arr.len(),    // Invariant for arr length
            first_elem_arr.len() == first_elem_arr.len(), // Invariant for first_elem_arr length
            index >= 0, // Invariant ensuring index is not under bound
            forall|i: int| 0 <= i < arr.len() ==> arr[i].len() > 0,  // Ensuring inner arrays have elements
    {
        let seq = &arr[index];
        first_elem_arr.push(seq[0]);
        index += 1;
    }
    first_elem_arr
}

} // verus!


//         first_elem_arr.push(seq[0]);
// failed precondition
//         i < vec.view().len(),
//   failed precondition: i < vec.view().len()
//   None: seq[0]

// Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True