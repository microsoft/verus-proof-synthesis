
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
                forall |k: int| 0 <= k < index ==> arr@[k] % 2 == 0,
                index < arr.len(),
                index >= 0, // Added by AI, for assertion fail
                index < arr.len(), // Added by AI, for assertion fail
            {
            assert(index < arr.len()); // Added by AI
            if (arr[index] % 2 == 0) {
                even_numbers.push(arr[index]);
            }
            index += 1;
            assert(index < arr.len()); // Added by AI
        }
        even_numbers
    }
} // verus!


//         assert(index < arr.len()); // Added by AI
//   assertion failed: index < arr.len()

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4
// Safe: True