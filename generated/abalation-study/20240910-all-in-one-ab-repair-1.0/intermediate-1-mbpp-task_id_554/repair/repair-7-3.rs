
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
        ensures
            odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0), // ensuring the expected behavior of returning filtered (odd) numbers based on the prove definitions
    
        {
        let mut odd_numbers: Vec<u32> = Vec::new();
        let input_len = arr.len();
        let mut index = 0;

        while index < arr.len()
             invariant
                index <= arr.len(),
                arr.len() == input_len,
                odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
        {
            if arr[index] % 2 != 0 {
                odd_numbers.push(arr[index]);
                proof {
                    // We ensure odd_numbers invariant checks with that it includes all odd numbers of arr
                }
            }
            index += 1;

        }
        odd_numbers // returning the results
      }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpeka1i6zl`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: False