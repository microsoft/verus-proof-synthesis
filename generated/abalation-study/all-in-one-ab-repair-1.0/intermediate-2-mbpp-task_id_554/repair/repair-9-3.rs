
use vstd::prelude::*;
fn main() {}

verus! {
    fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
        ensures
            // Postcondition: the resulting vector should contain only odd numbers from the input vector
            odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
    {
        let mut odd_numbers: Vec<u32> = Vec::new();
        let input_len = arr.len();
        let mut index = 0;

        while index < arr.len()
            invariant
                // Ensure that the index is always within the bounds of the array
                index as int <= arr@.len(),
                // Ensure that the odd_numbers vector contains all the odd numbers from the subrange of the input vector processed so far
                odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
                // Ensure that the length of the input vector remains constant
                arr.len() == input_len,
        {
            if arr[index] % 2 != 0 {
                odd_numbers.push(arr[index]);
                proof {
                    // Proof invariant: re-assert the relationship between odd_numbers and the subrange of arr
                    assert(odd_numbers@ == arr@.subrange(0, (index + 1) as int).filter(|x: u32| x % 2 != 0));
                }
            }
            index += 1;
        }

        // Postcondition proof: assert that the final odd_numbers vector contains all odd numbers from the input vector
        proof {
            assert(odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0));
        }

        odd_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp0jo3kxd3`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 4
// Safe: False