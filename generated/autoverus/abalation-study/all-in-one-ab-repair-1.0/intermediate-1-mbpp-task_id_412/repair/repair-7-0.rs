
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
                even_list.len() <= index, // even_list growing should not exceed the current index
                even_list.len() <= input_len, // even_list should never exceed original input length
                index < n && index <= arr.len(), // index within bounds
                arr.len() == input_len, // array length remains constant
                even_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0), // ensures correctness of the filtered sequence
        {
            if (arr[index] % 2 == 0) {
                even_list.push(arr[index]);
            }
            index += 1;
        }
        even_list
    }
}

Ensure you run the verification tool with the appropriate commands initiated for verifying this function with required flags and additional debugging if necessary. Here's an example execution:

sh
verus --verify=myfile.rs --multiple-errors=10


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpgexlatq1`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False