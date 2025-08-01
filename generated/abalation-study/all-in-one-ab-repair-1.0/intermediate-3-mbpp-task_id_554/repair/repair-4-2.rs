
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
            if (arr[index] % 2 != 0) {
                odd_numbers.push(arr[index]);
                proof {
                    let new_seq = odd_numbers@;
                    let arr_subrange = arr@.subrange(0, index as int);
                    assert(new_seq == arr_subrange.filter(|x: u32| x % 2 != 0).push(arr@[index as int]));
                }
            }
            index += 1;
            proof {
                let arr_subrange = arr@.subrange(0, index as int);
                assert(odd_numbers@ == arr_subrange.filter(|x: u32| x % 2 != 0));
            }
        }
        proof {
            assert(odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0));
        }
        odd_numbers
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpi8odoy9j`)
// 

// Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3
// Safe: True