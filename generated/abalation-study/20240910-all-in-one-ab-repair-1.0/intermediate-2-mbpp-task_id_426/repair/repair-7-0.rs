
use vstd::prelude::*;
fn main() {}

// Verus annotations
verus! {
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
                arr.len() == input_len,
                odd_list@ == arr@.subrange(0, index as int).filter(|x| *x % 2 != 0),
        {
            if arr[index] % 2 != 0 {
                odd_list.push(arr[index]);
            }
            index += 1;
            proof {
                assert(arr.len() == input_len); // Verifies that the length of arr never changes.
                assert(odd_list@ == arr@.subrange(0, index as int).filter(|x| *x % 2 != 0)); // Reaffirm the invariant.
            }
        }
        proof {
            assert(odd_list@ == arr@.filter(|x| *x % 2 != 0)); // Ensure the final condition is met.
        }
        odd_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp5_68pi2h`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False