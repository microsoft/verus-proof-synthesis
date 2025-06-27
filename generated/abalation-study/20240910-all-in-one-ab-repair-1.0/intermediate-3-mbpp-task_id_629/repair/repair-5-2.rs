
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn is_even(x: u32) -> bool {
        x % 2 == 0
    }

    fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
        ensures
            even_numbers@ == arr@.filter(is_even),
    {
        let mut even_numbers: Vec<u32> = Vec::new();
        let mut index = 0;
        while index < arr.len()
            invariant
                even_numbers@ == arr@.subrange(0, index as int).filter(is_even),
                index <= arr.len(),
        {
            if arr[index] % 2 == 0 {
                even_numbers.push(arr[index]);
            }
            index += 1;
        }

        even_numbers
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp4m8r4738`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False