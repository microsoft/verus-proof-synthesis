
use vstd::prelude::*;
fn main() {}

verus! {
    
proof fn filtered_array_contains_even_numbers(arr: &Vec<u32>, even_numbers: &Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
        forall |i| 0 <= i < even_numbers.len() ==> arr.contains(( even_numbers[i] ) as &u32),
{
    assert(even_numbers@.is_empty());
}

#[verifier::loop_isolation(false)]
fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
        forall |i| 0 <= i < even_numbers.len() ==> arr.contains(even_numbers[i]),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    proof {
        filtered_array_contains_even_numbers(arr, &even_numbers);
    }
    while index < arr.len()
        invariant
            index <= arr.len(),
            even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
            forall |i| 0 <= i < even_numbers.len() ==> arr.contains(even_numbers[i]),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }
        index += 1;
        filtered_array_contains_even_numbers(arr, &even_numbers);
    }
    proof {
        filtered_array_contains_even_numbers(arr, &even_numbers);
    }
    even_numbers
}
} // verus!



//     assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
//   assertion failed: even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False