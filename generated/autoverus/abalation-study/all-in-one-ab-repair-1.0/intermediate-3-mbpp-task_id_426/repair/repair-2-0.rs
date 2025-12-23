
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
            0 <= index <= arr.len(),  // Corrected invariant
            odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
            arr.len() == input_len,
    {
        if (arr[index] % 2 != 0) {
            odd_list.push(arr[index]);
        } else {
            proof {
               assert(arr[index] % 2 == 0);  // Added to help with proof
            }
        }
        index += 1;
        proof {
            // This is to assert the invariants at the end of each step.
            assert(0 <= index && index <= arr.len());
            assert(odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0));
        }
    }
    odd_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp2en13zo7`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False