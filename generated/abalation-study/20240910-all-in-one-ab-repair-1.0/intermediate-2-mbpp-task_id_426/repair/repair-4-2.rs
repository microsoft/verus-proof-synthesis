
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
    while index <= arr.len() // Changed to less than or equal to cover the range explicitly
        invariant
            index <= arr.len(),
            odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
            arr.len() == input_len,
    {
        if index < arr.len() && arr[index] % 2 != 0 { // Added boundary check inside if statement
            odd_list.push(arr[index]);
        }
        index += 1;
    }
    odd_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpa0p11h83`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4
// Safe: False