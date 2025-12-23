
use vstd::prelude::*;

fn main() {}

verus! {
    #[verifier::loop_isolation(false)]

    /// Helper function to prove the relationship between even_numbers and the input array.
    proof fn even_numbers_invariant(arr: &Vec<u32>, even_numbers: &Vec<u32>, index: u32)
        requires index <= arr.len(),
        ensures even_numbers@.ext_equal(arr@.filter(|x: u32| x % 2 == 0).take(index)),
        decreases arr.len() - index
    {
        if index < arr.len() {
            if arr[index as usize] % 2 == 0 {
                even_numbers_invariant(arr, even_numbers, index + 1);
                assert even_numbers@.ext_equal(arr@.filter(|x: u32| x % 2 == 0).take(index + 1));
            } else {
                even_numbers_invariant(arr, even_numbers, index + 1);
                assert even_numbers@.ext_equal(arr@.filter(|x: u32| x % 2 == 0).take(index));
            }
        } else {
            assert even_numbers@.ext_equal(arr@.filter(|x: u32| x % 2 == 0));
        }
    }

    /// Main function to find even numbers in the input array.
    fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
        ensures even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)
    {
        let mut even_numbers: Vec<u32> = Vec::new();
        let mut index = 0;
        even_numbers_invariant(arr, &even_numbers, index);
        while index < arr.len()
            invariant index <= arr.len()
        {
            if (arr[index] % 2 == 0) {
                even_numbers.push(arr[index]);
                even_numbers_invariant(arr, &even_numbers, index + 1);
            } else {
                even_numbers_invariant(arr, &even_numbers, index + 1);
            }
            index += 1;
            even_numbers_invariant(arr, &even_numbers, index);
        }
        even_numbers_invariant(arr, &even_numbers, arr.len() as u32);
        even_numbers
    }
} // verus!


//     assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
//   assertion failed: even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False