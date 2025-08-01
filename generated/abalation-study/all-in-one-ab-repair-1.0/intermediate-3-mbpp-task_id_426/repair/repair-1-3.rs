
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
        ensures
            odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
    {
        let mut odd_list: Vec<u32> = Vec::new();
        let input_len = arr.len();
        let mut index = 0;
        while index < arr.len()
            invariant
                index <= arr.len(),
                // Removed "index < arr.len()" as it may conflict with "index <= arr.len()"
                odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
                arr.len() == input_len,
        {
            if arr[index] % 2 != 0 {
                odd_list.push(arr[index]);
                proof {
                    // Validate that the odd_list is still a filtered subrange of arr
                    assert(odd_list@ == arr@.subrange(0, (index + 1) as int).filter(|x: u32| x % 2 != 0));
                }
            }
            index += 1;
        }
        odd_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp60bj0pdj`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4
// Safe: False