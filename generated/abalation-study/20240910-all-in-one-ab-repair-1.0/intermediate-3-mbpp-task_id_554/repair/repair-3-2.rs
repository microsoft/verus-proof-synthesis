
use vstd::prelude::*;
fn main() {}

verus! {
    fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
        ensures
            odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
    {
        let mut odd_numbers: Vec<u32> = Vec::new();
        let input_len = arr.len();
        
        if input_len == 0 {
            return odd_numbers;
        }
        
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
                    let new_seq = Seq::<u32>::empty().push(0); // we need a valid sequence for generalization
                    assert(new_seq.filter(|x: u32| x % 2 != 0).len() <= new_seq.len()); // ensure the filter function is defined correctly for the vector
                }
            }
            index += 1;
        }

        proof {
            let final_seq = arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0); 
            assert(final_seq == odd_numbers@);
        }
        
        odd_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpdji3hqbp`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 4
// Safe: False