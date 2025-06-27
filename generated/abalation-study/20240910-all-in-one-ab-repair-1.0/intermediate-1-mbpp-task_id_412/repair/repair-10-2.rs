
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
        while index < arr.len()
            invariant
                even_list.len() <= index, // even_list growing should not exceed the current index
                even_list.len() <= input_len, // even_list should never exceed original input length
                index <= arr.len(),  // index should stay within the bounds
                arr.len() == input_len, // array length remains constant
                even_list@.len() <= index as int,
                even_list@.len() <= arr@.len(),
                forall|i: int| 0 <= i < even_list.len() ==> even_list@[i] % 2 == 0, // all elements in even_list are even
                forall|j: int| 0 <= j < index ==> (
                    if arr@[j] % 2 == 0 {
                        even_list@.contains(|k: u32| k == arr@[j])
                    } else {
                        true
                    }
                ),
        {
            if arr[index] % 2 == 0 {
                even_list.push(arr[index]);
                proof {
                    assert(even_list@.len() == (even_list.len() - 1) as int);
                    // Assert the new element added is the correct one and the length is updated properly
                    assert(even_list@ == even_list@.update((even_list.len() as int) - 1, arr@[index as int]));
                }
            }
            index += 1;
            proof {
                assert(index <= input_len);
            }
        }
        proof {
            assert(even_list@ == arr@.filter(|x: u32| x % 2 == 0));
        }
        even_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpre6jtzs9`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False