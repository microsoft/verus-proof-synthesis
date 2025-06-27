
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

        while index < input_len
            invariant
                input_len == arr.len(),
                index <= input_len,
                odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
        {
            if arr[index] % 2 != 0 {
                odd_numbers.push(arr[index]);

                // Ensure after pushing the invariant still holds
                proof {
                    assert(odd_numbers@.len() <= index as int + 1);
                    assert(odd_numbers@ == arr@.subrange(0, index as int + 1).filter(|x: u32| x % 2 != 0));
                }
            }
            index += 1;
        }

        // Ensure that after the loop, the output condition is satisfied
        proof {
            assert(odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0));
        }

        odd_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp48_74u4n`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 4
// Safe: False