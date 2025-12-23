
use vstd::prelude::*;
fn main() {}

verus! {

fn filter_odd_numbers(arr: &Vec<u32>) -> Vec<u32>
    ensures
        // Ensures that the resulting vector only contains the odd numbers from the original
        arr@.intersect(#[trigger] arr@.filter(|x: u32| x % 2 != 0)) == arr@.filter(|x: u32| x % 2 != 0),
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
        if arr[index] % 2 != 0 {
            odd_list.push(arr[index]);
        }
        index += 1;
    }
    odd_list
}

} // verus!



// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp58t9_lkk`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False