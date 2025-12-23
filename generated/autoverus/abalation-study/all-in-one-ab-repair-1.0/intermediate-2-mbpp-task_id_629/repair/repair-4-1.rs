
use vstd::prelude::*;
fn main() {}

verus! {

    #[verifier::loop_isolation(false)]
    fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
        ensures
            even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
    {
        let mut even_numbers: Vec<u32> = Vec::new();

        // Added by AI: Proper initialization of ghost variables for proof
        let ghost original_arr = arr@;
        let ghost even_seq_init = Seq::<u32>::empty();

        let mut index = 0;
        while index < arr.len()
            invariant
                even_numbers@ == original_arr.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
                index <= arr.len(),
                arr.len() == arr.len(), // redundant invariant, but semantically correct, can remove it
                exists|r: Seq<int>| is_reorder_of(r, original_arr, arr@), // Correct invariant for reordering
        {
            if arr[index] % 2 == 0 {
                even_numbers.push(arr[index]);
                proof {
                    // Maintain loop invariant for the sequence property
                    let new_seq = even_seq_init.push(arr[index]);
                    assert(even_numbers@ == new_seq);
                }
            }
            index += 1;
            // Ensure continued validity of loop invariants
            proof {
                assert(index <= arr.len());
                assert(arr.len() == original_arr.len());
                assert(even_numbers@ == original_arr.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
            }
        }
        even_numbers
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpnd4pnxmh`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False