
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
        // Extract the value at index and convert it to the mirrored data type used for verification.
        let value = arr[index];
        let ghost arr_seq = arr@;
        let ghost even_list_seq = even_list@;
        if value % 2 == 0 {
            even_list.push(value);
            proof {
                // Update the ghost variable for even_list
                let ghost new_even_list_seq = even_list_seq.push(value);
                assert(new_even_list_seq == even_list@); // Ensure even_list@ is updated correctly
            }
        }
        index += 1;
    }
    proof {
        // Final assertion to ensure even_list@ matches the expected filtered sequence
        assert(even_list@ == arr@.filter(|x: u32| x % 2 == 0));
    }
    even_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp8q2t9b_k`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: False