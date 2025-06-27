
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
        while index < arr.len()
            invariant
                even_list.len() <= index,
                even_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
                index <= arr.len(),
                arr.len() == input_len,
                even_list.len() <= input_len,
        {
            if (arr[index] % 2 == 0) {
                even_list.push(arr[index]);
            }
            index += 1;
        }
        even_list
    }
}

Given that the code appears to be correct from a logical verification standpoint, you might want to rationalize how you are executing the program with the Verus tool. Make sure your files are appropriately set up and you're not providing multiple conflicting input filenames.

If the method of invocation looks something like this:
verus my_code.rs
/tmp/tmpxyghwac2

Ensure you avoid supplying multiple filenames or paths unless the tool explicitly supports it.

Alternatively, you might find it useful to execute the `verus` command only on your intended source file:
verus my_code.rs


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmputltuuqf`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False