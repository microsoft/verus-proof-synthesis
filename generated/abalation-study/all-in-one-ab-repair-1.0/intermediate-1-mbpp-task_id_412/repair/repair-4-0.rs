
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn remove_odds(arr: &Vec<u32>) -> Vec<u32> 
        ensures
            result@ == arr@.filter(|x: u32| x % 2 == 0),
    {
        let mut even_list: Vec<u32> = Vec::new();
        let input_len = arr.len();
        let mut index = 0;
        while index < arr.len()
            invariant
                even_list.len() <= index, // even_list growing should not exceed the current index
                even_list.len() <= input_len, // even_list should never exceed original input length
                index <= arr.len(),  // index should stay within the bounds
                arr.len() == input_len, // array length remains constant
                even_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0), // ensures correctness of the filtered sequence
        {
            if arr[index] % 2 == 0 {
                even_list.push(arr[index]);
            }
            index += 1;
        }
        even_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp_uu5w61t`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False