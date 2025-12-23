
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn is_even(x: u32) -> bool {
        x % 2 == 0
    }

    fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
        ensures
            even_numbers@ == arr@.filter(|x: &u32| is_even(*x)),
    {
        let mut even_numbers: Vec<u32> = Vec::new();
        let mut index = 0;
        while index < arr.len()
            invariant
                even_numbers@ == arr@.subrange(0, index as int).filter(|x: &u32| is_even(*x)),
                index <= arr.len(),
                arr.len() == old(arr.len()),
                forall |k: int| 0 <= k < arr.len() ==> arr[k] == old(arr[k]), // Added because arr is not modified in the loop
        {
            if arr[index] % 2 == 0 {
                even_numbers.push(arr[index]);
            }
            index += 1;
        }
        even_numbers
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpggj1dp1_`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False