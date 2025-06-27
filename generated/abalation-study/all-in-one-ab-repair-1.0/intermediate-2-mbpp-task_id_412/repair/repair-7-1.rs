
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
        let ghost original_list = arr@; // Added ghost variable to track the original logical view of arr
        while index < arr.len()
            invariant
                even_list.len() <= index, // ensures length of even_list doesn't exceed the current index
                even_list@ == original_list.subrange(0, index as int).filter(|x: u32| x % 2 == 0), // maintains view of filtered elements
                index <= arr.len(), // ensures index stays within bounds of arr
                arr.len() == input_len, // ensures length of arr doesn't change
                even_list.len() <= input_len, // ensures the length of even_list doesn't exceed arr length
        {
            if arr[index] % 2 == 0 {
                even_list.push(arr[index]);
            }
            index += 1;
        }
        // Post-condition assert to ensure final state meets specified conditions
        proof {
            assert!(even_list@ == original_list.filter(|x: u32| x % 2 == 0));
        }
        even_list
    }

}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpxc5skg12`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False