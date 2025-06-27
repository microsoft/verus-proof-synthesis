
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
                arr.len() == input_len,
        {
            if arr[index] % 2 != 0 {
                odd_numbers.push(arr[index]);
                proof {
                    assert(odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0).push(arr[index]));
                }
            }
            index += 1;
        }

        // Proof block for ensuring the invariant holds at the end of the loop
        proof {
            let subseq = arr@.subrange(0, index as int);
            let filtered_subseq = subseq.filter(|x: u32| x % 2 != 0);
            assert(odd_numbers@ == filtered_subseq);
        }

        odd_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpgre_fdgp`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False