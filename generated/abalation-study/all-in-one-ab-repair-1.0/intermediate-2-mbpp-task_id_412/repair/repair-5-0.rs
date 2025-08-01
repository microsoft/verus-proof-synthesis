
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
                even_list.len() <= index,
                even_list@ == original_list.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
                index <= arr.len(),
                arr.len() == input_len,
                even_list.len() <= input_len,
        {
            if arr[index] % 2 == 0 {
                even_list.push(arr[index]);
                proof {
                    assert(even_list@ == original_list.subrange(0, index as int + 1).filter(|x: u32| x % 2 == 0));
                }
            }
            index += 1;
            // Updating the invariant assertion for the new index value
            proof {
                assert(even_list.len() <= index);
                assert(even_list@ == original_list.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
            }
        }
        even_list
    }

}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpz462cl_i`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4
// Safe: False