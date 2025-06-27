
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
                odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
                arr.len() == input_len,
        {
            if (arr[index] % 2 != 0) {
                proof {
                    // Maintain the invariants after pushing to the Vec
                    let new_len = odd_list.len() + 1;
                    let ghost mut temp_odd_list = odd_list@.push(arr[index]);
                    let old_index = index as int;
                    assert(temp_odd_list.len() == new_len as int);
                    assert(temp_odd_list[old_index] == arr[index]);
                    assert(temp_odd_list == odd_list@.push(arr@[index as int]));
                } // Added by AI
                odd_list.push(arr[index]);
            }
            index += 1;
            proof {
                // Maintain the invariants after incrementing index
                assert(odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0));
            } // Added by AI
        }
        odd_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp5u35k7vc`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True