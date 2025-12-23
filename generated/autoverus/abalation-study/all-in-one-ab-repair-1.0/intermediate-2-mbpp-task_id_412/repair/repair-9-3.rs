
use vstd::prelude::*;
fn main() {}

verus! {

    #[verifier::proof_function]
    fn filter_even(a: Seq<u32>) -> Seq<u32> {
        a.filter(|x| *x % 2 == 0)
    }

    fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
        ensures
            even_list@ == arr@.filter(|x: u32| x % 2 == 0),
    {
        let mut even_list: Vec<u32> = Vec::new();
        let input_len = arr.len();
        let mut index = 0;
        let ghost original_list = arr@; // Added ghost variable to track the original logical view of arr

        while index < arr.len()
            invariant
                even_list.len() <= index,
                even_list@ == original_list.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
                index <= arr.len(),
                arr.len() == input_len,
                even_list.len() <= input_len,
        {
            if arr[index] % 2 == 0 {
                even_list.push(arr[index]);
                proof {
                    // Ensuring the invariant: after pushing, even_list.length() <= index + 1
                    assert(even_list.len() <= index + 1);
                }
            }
            index += 1;
        }

        proof {
            // Ensuring the final postcondition
            assert(even_list@ == original_list.filter(|x: u32| x % 2 == 0));
        }

        even_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp9xzd9zgl`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False