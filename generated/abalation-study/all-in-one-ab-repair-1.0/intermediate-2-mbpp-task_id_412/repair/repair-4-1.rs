
use vstd::prelude::*;
fn main() {}

verus! {

    fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
        ensures
            even_list@ == arr@.filter(|x: u32| x % 2 == 0),
    {
        let mut even_list: Vec<u32> = Vec::new();
        let input_len = arr.len();
        let mut index = 0;
        let ghost original_list = arr@; // Add ghost variable to track the original logical view of arr
        while index < arr.len()
            invariant
                even_list.len() <= index,
                even_list@ == original_list.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
                index <= arr.len(),
                arr.len() == input_len,
                even_list.len() <= input_len,
        {
            if arr[index] % 2 == 0 {
                proof {
                    // The following is a proof block that asserts maintaining the invariants
                    let original_len = even_list.len();
                    let updated_len = original_len + 1;
                    assert(updated_len @== original_len + 1);
                }
                even_list.push(arr[index]);
                proof {
                    // After pushing, we have to assert that the invariant even_list@ is as per the rule
                    assert(even_list.len() == index + 1);
                    assert(even_list@ == original_list.subrange(0, (index + 1) as int).filter(|x: u32| x % 2 == 0));
                }
            }
            index += 1;
            proof {
                // Maintain invariants after updating the index
                assert(even_list.len() <= index);
                assert(arr.len() == input_len);
                assert(index <= arr.len());
                assert(even_list.len() <= input_len);
            }
        }
        even_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmprnqbxy2_`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False