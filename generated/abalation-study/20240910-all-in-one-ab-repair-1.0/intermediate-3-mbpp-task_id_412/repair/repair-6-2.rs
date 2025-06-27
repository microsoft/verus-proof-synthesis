
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
        if arr[index] % 2 == 0 {
            even_list.push(arr[index]);
            proof {
                // We must establish that after pushing, the length of even_list is as expected
                assert(even_list.len() == even_list@.len() as usize);
            }
        }
        index += 1;
    }
    even_list
}

}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpmox8bqe2`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: False