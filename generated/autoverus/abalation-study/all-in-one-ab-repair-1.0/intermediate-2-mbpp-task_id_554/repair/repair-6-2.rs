
use vstd::prelude::*;
fn main() {}

verus! {
    fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
        ensures
            odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
    {
        let mut odd_numbers: Vec<u32> = Vec::new();
        let input_len = arr.len();
        let mut index = 0;

        while index < arr.len()
            invariant
                arr.len() == input_len,
                0 <= index <= arr.len(),
                odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
        {
            // Mutual Exclusion Proof (for Futher Assurance, If Needed)
            proof {
                assert(arr.len() == input_len);
                assert(0 <= index);
                assert(index <= arr.len());
                assert(odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0));
            }

            if arr[index] % 2 != 0 {
                odd_numbers.push(arr[index]);
            }
            index += 1;
        }

        // Proof block to ensure final condition after the loop
        proof {
            assert(odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0));
        }

        odd_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpqw0dtsaw`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3
// Safe: False