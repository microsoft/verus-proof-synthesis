
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
        ensures
            even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
    {
        let mut even_numbers: Vec<u32> = Vec::new();
        let mut index = 0;
        while index < arr.len()
            invariant
                even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
                index <= arr.len(),
                forall |k: int| 0 <= k < index ==> arr@.contains(arr[k]), // Maintain that arr[k] is in the array
        {
            if arr[index] % 2 == 0 {
                proof {
                    let current_len = even_numbers.len(); // Get current length of even_numbers
                    assert(current_len as int == even_numbers@.len());
                    let new_len = current_len + 1; // This will be the new length after push
                    assert(new_len as int == even_numbers.push(arr[index])@.len());
                }
                even_numbers.push(arr[index]);
            }

            proof {
                let current_index = index as int;
                assert(current_index < arr.len() as int);
                let subrange_until_now = arr@.subrange(0, current_index + 1); // This covers elements from 0 to 'index' inclusive
                let filtered_even = subrange_until_now.filter(|x: u32| x % 2 == 0);
                assert(even_numbers@ == filtered_even);
            }
            index += 1;
        }
        even_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp66vf7yj_`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False