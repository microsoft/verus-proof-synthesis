
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
        {
            if (arr[index] % 2 == 0) {
                proof {
                    // Here, we can assert that even_numbers will be updated correctly
                    let new_even_numbers = even_numbers@.push(arr[index]); // Temporarily hold the updated sequence
                    assert(new_even_numbers == arr@.subrange(0, index as int + 1).filter(|x: u32| x % 2 == 0));
                }
                even_numbers.push(arr[index]);
            }
            // Increment the index at the end of the loop iteration block
            index += 1;
        }
    
        // Returning even_numbers at the end
        even_numbers
    }
} // verus!

A few points to note:
- Ensures clause:
  ensures even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),

// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpubxrrxac`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False