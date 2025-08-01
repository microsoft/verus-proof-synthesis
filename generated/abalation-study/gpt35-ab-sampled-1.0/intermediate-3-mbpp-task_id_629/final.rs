
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
    {
        reveal(Seq::filter); // Added reveal command to assist Verus in understanding filter
        let mut even_numbers: Vec<u32> = Vec::new();
        let mut index = 0;
        assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
        while index < arr.len()
            invariant
                index <= arr.len(),
        {
            if (arr[index] % 2 == 0) {
                even_numbers.push(arr[index]);
            }
            index += 1;
            assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
        }
        assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
        even_numbers
    }

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3