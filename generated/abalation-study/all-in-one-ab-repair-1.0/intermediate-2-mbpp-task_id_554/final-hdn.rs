
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
                index as int <= arr@.len(),
                arr.len() == input_len,
        {
            if (arr[index] % 2 != 0) {
                odd_numbers.push(arr[index]);
            }
            index += 1;
        }

        proof {
        }

        odd_numbers
    }
}


// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1