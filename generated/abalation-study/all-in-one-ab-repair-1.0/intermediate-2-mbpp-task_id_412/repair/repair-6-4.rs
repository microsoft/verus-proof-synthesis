
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
        
        // Add ghost variable to track the original logical view of arr
        let ghost original_list = arr@;
        
        while index < arr.len()
            invariant
                even_list.len() <= index,
                index <= arr.len(),
                even_list@ == original_list.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
                arr.len() == input_len,
                even_list.len() <= input_len,
        {
            if arr[index] % 2 == 0 {
                even_list.push(arr[index]);
            }
            index += 1;
        }
        
        even_list
    }

}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp9rfn6vf8`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3
// Safe: False