
use vstd::prelude::*;
fn main() {}

verus! {
    fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
        ensures
            odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
    {
        let mut odd_list: Vec<u32> = Vec::new();
        let input_len = arr.len();
        let mut index = 0;
        while index < arr.len()
            invariant
                index <= arr.len(),
                odd_list@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 != 0),
                arr.len() == input_len,
        {
            if arr[index] % 2 != 0 {
                proof {
                    let old_odd_list = odd_list@;
                    let old_subrange = arr@.subrange(0, index as int);
                    assert(old_odd_list.len() <= old_subrange.len());
                }
                odd_list.push(arr[index]);
                proof {
                    let new_odd_list = old_odd_list.push(arr[index]);
                    assert(new_odd_list == odd_list@);
                }
            }
            index += 1;
        }
        proof {
            assert(odd_list@ == arr@.filter(|x: u32| x % 2 != 0));
        }
        odd_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpbypjrsud`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False