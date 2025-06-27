
use vstd::prelude::*;
fn main() {}

verus! {
    fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
        ensures
            odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
    {
        let mut odd_numbers: Vec<u32> = Vec::new(); // Add by AI
        proof { // Added by AI
            assert(odd_numbers@ == Seq::<u32>::empty()); // Added by AI
        }
        let input_len = arr.len();
        let mut index = 0;
        while index < arr.len()
            invariant
                index as int <= arr@.len(),
                odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
                arr.len() == input_len,
        {
            if arr[index] % 2 != 0 {
                odd_numbers.push(arr[index]);
                proof { // Added by AI
                    assert(odd_numbers@ == arr@.subrange(0, index as int + 1).filter(|x: u32| x % 2 != 0));
                }
            }
            index += 1;
        }
        odd_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpssrs67j5`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 4
// Safe: False