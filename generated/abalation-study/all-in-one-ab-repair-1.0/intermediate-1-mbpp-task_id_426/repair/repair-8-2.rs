
use vstd::prelude::*;
fn main() {}

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
                odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
        {
            if (arr[index] % 2 != 0) {
                odd_list.push(arr[index]);
            }

            proof {
                // Update the invariant after pushing to the odd_list
                if arr[index] % 2 != 0 {
                    assert(odd_list@ == arr@.subrange(0, index as int + 1).filter(|x: u32| x % 2 != 0));
                } else {
                    assert(odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0));
                }
            }

            index += 1;

            proof {
                assert(index <= arr.len());
                assert(arr.len() == input_len);
                let ghost filtered_slice = arr@.subrange(0, index as int);
                assert(odd_list@ == filtered_slice.filter(|x: u32| x % 2 != 0));
            }
        }
        
        odd_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpwf9vy8jf`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True