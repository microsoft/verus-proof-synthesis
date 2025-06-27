
use vstd::prelude::*;
fn main() {}

verus! {

fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_list: Vec<u32> = Vec::new();
    let input_len = arr.len();
    let mut index = 0;

    while index < arr.len()
        invariant
            even_list.len() <= index as usize, // even_list growing should not exceed the current index
            even_list.len() <= input_len, // even_list should never exceed original input length
            index <= arr.len(),  // index should stay within the bounds
            arr.len() == input_len, // array length remains constant
            even_list@ == arr@[0..index].subrange(0, index as int).filter(|x: u32| x % 2 == 0), // ensures correctness of the filtered sequence
    {
        if arr[index] % 2 == 0 {
            even_list.push(arr[index]);
        }
        index += 1;
    }
    even_list
}
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmprk6_m6ni`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False