
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
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
                arr.len() == input_len, // Ensure the length of arr remains constant
        {
            if (arr[index] % 2 != 0) {
                odd_numbers.push(arr[index]);
                proof {
                    let updated_seq = arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0).push(arr[index]);
                    assert(odd_numbers@ == updated_seq);
                }
            }
            index += 1;
            proof {
                assert(odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0));
            }
        }
        odd_numbers
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpu124o7a6`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True