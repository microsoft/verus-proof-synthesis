
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
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
            arr.len() == arr.len(),
    {
        proof {
            assert(arr.len() == arr.len()); // Trivial invariant, but helpful for completeness.
            assert(index <= arr.len()); // Checking the upper bound invariant.
        }

        if arr[index] % 2 == 0 {
            even_numbers.push(arr[index]);
            proof {
                // Ensuring the invariant holds after pushing to even_numbers.
                assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0).push(arr[index]));
            }
        }

        index += 1;
    }
    even_numbers
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpu_q236j9`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False