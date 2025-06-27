
use vstd::prelude::*;
fn main() {}

verus! {

/// Helper function to prove that a given element satisfies the filter condition
proof fn is_even(x: u32)
    ensures x % 2 == 0
{
    // Prove that the element satisfies the condition
}

/// Helper function to prove that the resulting even numbers vector is correct
proof fn even_numbers_result(arr: &Vec<u32>, even_numbers: &Vec<u32>)
    ensures even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)
{
    assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)) by {
        let mut i = 0;
        while i < even_numbers.len()
            invariant i <= even_numbers.len()
            ensures i <= even_numbers.len()
        {
            assert(( is_even(even_numbers[i]) ) as bool); // Call the helper function to prove that each element in the resulting vector is even
            i += 1;
        }
    }
}

#[verifier::loop_isolation(false)]
fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    even_numbers_result(arr, &even_numbers); // Prove that the initial state satisfies the postcondition
    while index < arr.len()
        invariant
            index <= arr.len(),
            even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }
        index += 1;
        even_numbers_result(arr, &even_numbers); // Prove that the resulting vector is as expected after each iteration
    }
    even_numbers_result(arr, &even_numbers); // Prove that the resulting vector satisfies the postcondition
    even_numbers
}

} // verus!



//     assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
//   assertion failed: even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False