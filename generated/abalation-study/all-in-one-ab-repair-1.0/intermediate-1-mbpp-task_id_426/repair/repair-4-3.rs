
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn filter_predicate(x: u32) -> bool {
        x % 2 != 0
    }

    fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
        ensures
            odd_list@ == arr@.filter(|x: u32| filter_predicate(*x)),
    {
        let mut odd_list: Vec<u32> = Vec::new();
        let input_len = arr.len();
        let mut index = 0;
        while index < arr.len()
            invariant
                index <= arr.len(),
                odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| filter_predicate(*x)),
                arr.len() == input_len,
        {
            if (arr[index] % 2 != 0) {
                odd_list.push(arr[index]);
            }
            index += 1;
        }
        odd_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpvutkz8ak`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False