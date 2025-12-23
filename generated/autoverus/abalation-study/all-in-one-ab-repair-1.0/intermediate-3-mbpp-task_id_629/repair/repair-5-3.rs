
use vstd::prelude::*;
fn main() {}

verus! {

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    while index < arr.len()
        invariant
            even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
            index <= arr.len(),
            index >= 0, // Added by AI
    {
        if arr[index] % 2 == 0 {
            proof {
                let current = arr[index];
                let even_numbers_old = even_numbers@;
                even_numbers.push(current);
                assert(even_numbers@ == even_numbers_old.push(current)); // Proof the new state
            }
            even_numbers.push(arr[index]);
        }
        // Increment the index at the end of the loop iteration block
        index += 1;
        proof {
            assert(index <= arr.len()); // Always ensure index within length
            assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0)); // restate the invariant
        }
    }

    // Returning even_numbers at the end
    proof {
        assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0));
    }
    even_numbers
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmphd4xdzup`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False