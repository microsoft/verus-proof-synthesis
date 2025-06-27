
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_invariant]
    fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
        ensures
            odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
    {
        let mut odd_numbers: Vec<u32> = Vec::new();
        let input_len = arr.len();
        let mut index = 0;

        while index < arr.len()
            invariant
                index as int <= arr@.len(),
                odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
                arr.len() == input_len,
        {
            if (arr[index] % 2 != 0) {
                odd_numbers.push(arr[index]);
                proof {
                    assert(odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0).push(arr[index]));
                }
            }
            index += 1;
            proof {
                assert(odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0));
            }
        }

        proof {
            assert(odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0));
        }

        odd_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpctenugo7`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True