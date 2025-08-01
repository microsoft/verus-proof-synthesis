
use vstd::prelude::*;
fn main() {}

verus! {
    fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
        ensures
            even_list@ == arr@.filter(|x: u32| x % 2 == 0),
    {
        let mut even_list: Vec<u32> = Vec::new();
        let input_len = arr.len();
        let mut index = 0;
        while index < arr.len()
            invariant
                // Verifying list size constraints, ensuring they match their ghost versions
                even_list.len() <= index, 
                even_list.len() <= input_len,
                // Ensuring index stays within bounds and original array length is kept constant
                index <= arr.len(),  
                arr.len() == input_len,
                // Confirming ghost versions match the expected length values
                even_list@.len() as usize == even_list.len(),
                // Conforming that all collected even values match with their positions in the original array
                forall|i: int| 0 <= i < even_list.len() ==> even_list@[i] == arr@[i] && arr@[i] % 2 == 0,
        {
            if arr[index] % 2 == 0 {
                even_list.push(arr[index]);
            }
            index += 1;
        }
        even_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpelu1l03l`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: False