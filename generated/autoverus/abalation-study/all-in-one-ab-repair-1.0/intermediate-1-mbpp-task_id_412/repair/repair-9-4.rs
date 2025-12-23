
use vstd::prelude::*;
fn main() {}

verus! {
    fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
        ensures
            even_list@ == arr@.filter(|x: u32| x % 2 == 0),
    {
        let mut even_list: Vec<u32> = Vec::new();
        let input_len = arr.len();
        let mut index: usize = 0; // Explicitly specify the index as usize
        while index < arr.len()
            invariant
                even_list.len() <= index, // even_list growing should not exceed the current index
                even_list.len() <= input_len, // even_list should never exceed original input length
                index <= arr.len(),  // index should stay within the bounds
                arr.len() == input_len, // array length remains constant
                exists|j: int| 0 <= j <= index as int && even_list@ == arr@[0..index as int].filter(|x: u32| *x % 2 == 0),
        {
            if arr[index] % 2 == 0 {
                even_list.push(arr[index]);
                proof {
                    // Assertion for added element correctness
                    assert(even_list@.len() == even_list.len() as int);

                    let j = even_list.len() as int;
                    assert(even_list@.update(j - 1, arr@[index as int]) =~= even_list@.add(Seq::singleton(arr@[index as int])));
                }
            }
            index += 1;
        }
        proof {
            assert(even_list@ == arr@.filter(|x: u32| *x % 2 == 0));
        }
        even_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpr4len4ze`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: False