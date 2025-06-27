
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
        let mut index: usize = 0;

        while index < arr.len()
            invariant
                index as int <= arr@.len(),
                odd_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
                arr.len() == input_len,
        {
            if arr[index] % 2 != 0 {
                odd_numbers.push(arr[index]);
                proof {
                    let start_subrange = arr@.subrange(0, index as int);
                    let end_subrange = arr@.subrange(index as int, arr@.len());
                    let filtered_start = start_subrange.filter(|x: u32| x % 2 != 0);

                    // Verify the update to odd_numbers@
                    assert(odd_numbers@ == filtered_start.push(arr@[index as int]));
                    assert(odd_numbers@ == filtered_start);
                }
            }
            index += 1;
        }
        odd_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp8po4ru0q`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False