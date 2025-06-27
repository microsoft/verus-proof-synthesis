
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
                index <= arr.len(),
                odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
                odd_numbers@.len() <= index as int,
                arr.len() == input_len,
        {
            if (arr[index] % 2 != 0) {
                odd_numbers.push(arr[index]);
                proof {
                    // Ensure the invariant about odd_numbers being correctly updated
                    let filtered_len = arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0).len() + 1;
                    assert(odd_numbers@.len() == filtered_len);
                }
            }
            index += 1;
        }
        proof {
            // Final proof to ensure postcondition is satisfied
            assert(odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0));
        }
        odd_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpyytmuvu_`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3
// Safe: True