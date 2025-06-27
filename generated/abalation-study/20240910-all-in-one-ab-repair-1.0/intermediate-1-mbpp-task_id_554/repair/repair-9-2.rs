
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
                arr.len() == input_len, // Ensure the length of arr remains constant
        {
            if arr[index] % 2 != 0 {
                odd_numbers.push(arr[index]);
                proof {
                    let ghost old_odd_numbers = odd_numbers@.take(odd_numbers.len()-1);
                    let ghost updated_odd_numbers = old_odd_numbers.push(arr[index]);
                    assert!((updated_odd_numbers == old_odd_numbers.push(arr[index])).ensures(
                        updated_odd_numbers == odd_numbers@));
                    assert(odd_numbers@ == arr@.subrange(0, index as int + 1).filter(|x: u32| x % 2 != 0));
                }
            }
            index += 1;
        }
        odd_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpa2xhdt9f`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False