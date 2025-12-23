
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
            even_list.len() <= index, // The even_list cannot be longer than the current index
            even_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0), // Even list matches the filtered subrange
            index <= arr.len(), // Index is always within the original array length
            arr.len() == input_len, // The length of the original array hasn’t changed
            even_list.len() <= input_len, // The even_list length should not exceed input length
    {
        if arr[index] % 2 == 0 {
            even_list.push(arr[index]);
        }
        index += 1;
    }
    even_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp2h8uki_s`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: False