
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn is_even(n: u32) -> bool {
        n % 2 == 0
    }

    #[verifier::loop_isolation(false)]
    fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
        ensures
            even_list@ == arr@.filter(|x: u32| is_even(*x)),
    {
        let mut even_list: Vec<u32> = Vec::new();
        let input_len = arr.len();
        let mut index = 0;
        while index < arr.len()
            invariant
                even_list.len() <= index,
                even_list@ == arr@.subrange(0, index as int).filter(|x: u32| is_even(*x)),
                index <= arr.len(),
                arr.len() == input_len,
        {
            if is_even(arr[index]) {
                even_list.push(arr[index]);
            }
            index += 1;
        }
        even_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpsy6ysnvz`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False