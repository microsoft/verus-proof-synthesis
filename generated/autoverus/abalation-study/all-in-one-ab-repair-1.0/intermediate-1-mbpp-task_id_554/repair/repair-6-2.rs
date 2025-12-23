
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
            if arr[index] % 2 != 0 {
                odd_numbers.push(arr[index]);
                proof {
                    // verifying the length after the push
                    let updated_len = odd_numbers.len() as int;
                    // filtering odd numbers up to current index
                    let filtered_seq = arr@.subrange(0, index as int + 1).filter(|x: u32| x % 2 != 0);
                    // verifying push has modified sequence correctly
                    assert(odd_numbers@ == filtered_seq);
                    assert(odd_numbers.len() == updated_len as nat);
                }
            }
            index += 1;
        }
        odd_numbers
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpzi64jex1`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4
// Safe: False