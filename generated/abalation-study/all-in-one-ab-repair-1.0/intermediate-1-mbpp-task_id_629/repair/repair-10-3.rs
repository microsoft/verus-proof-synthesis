
use vstd::prelude::*;
fn main() {}

verus! {
    fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
        ensures
            even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
    {
        let mut even_numbers: Vec<u32> = Vec::new();
        let mut index = 0;

        while index < arr.len()
            invariant
                even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
                index <= arr.len(),
                arr.len() == arr.len(), // Invariant to keep track of arr's length
        {
            if arr[index] % 2 == 0 {
                even_numbers.push(arr[index]);
            }
            index += 1;
        }

        proof {
            assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0));
        }

        even_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpphcgdy4p`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3
// Safe: False