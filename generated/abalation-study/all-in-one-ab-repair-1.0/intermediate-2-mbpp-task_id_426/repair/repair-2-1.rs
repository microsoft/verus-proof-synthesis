
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
            input_len == arr.len(), // Added invariant to maintain input length
            odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
    {
        if arr[index] % 2 != 0 {
            proof {
                let new_value = arr[index];
                let new_list = odd_list@.push(arr[index]);
                assert(new_list == arr@.subrange(0, (index + 1) as int).filter(|x: u32| x % 2 != 0));
            }
            odd_list.push(arr[index]);
        }
        index += 1;
    }
    odd_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp_n2qcvub`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False