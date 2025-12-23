
use vstd::prelude::*;
fn main() {}

verus! {

    #[verifier::loop_isolation(false)]
    fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
        ensures
            even_list@ == arr@.filter(|x: u32| x % 2 == 0),
    {
        let mut even_list: Vec<u32> = Vec::new();
        let input_len = arr.len();
        let mut index = 0;
        let ghost original_list = arr@; // Add ghost variable to track the original logical view of arr
        while index < arr.len()
            invariant
                even_list.len() <= index, // Ensure even_list does not exceed the processed part of arr
                even_list@ == original_list.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
                index <= arr.len(),
                arr.len() == input_len,
                even_list.len() <= input_len,
        {
            if arr[index] % 2 == 0 {
                even_list.push(arr[index]);
            }
            index += 1;
        }
        proof {
            assert(even_list@ == arr@.filter(|x: u32| x % 2 == 0)); // Added to ensure postcondition
        }
        even_list
    }

}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpml8z77ze`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: False