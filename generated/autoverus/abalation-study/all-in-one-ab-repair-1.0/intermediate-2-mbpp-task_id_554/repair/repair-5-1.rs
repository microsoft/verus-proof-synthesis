
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn filter_odd(arr: Seq<u32>) -> Seq<u32> {
        arr.filter(|x: u32| x % 2 != 0)
    }

    #[verifier::loop_isolation(false)]
    fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
        ensures
            odd_numbers@ == filter_odd(arr@),
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
            if arr[index] % 2 != 0 {
                odd_numbers.push(arr[index]);
            }
            index += 1;
        }
        odd_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpp6758mi8`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: False