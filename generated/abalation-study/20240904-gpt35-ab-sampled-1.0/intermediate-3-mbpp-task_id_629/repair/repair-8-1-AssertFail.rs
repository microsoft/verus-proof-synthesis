
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

/// A helper function to prove that the resulting vector contains only even numbers from the input vector
proof fn even_numbers_filter(arr: Vec<u32>)
    ensures forall |x| #[trigger] arr.contains(x) && (x % 2 == 0) <==> even_numbers_filter(arr).contains(x)
{
    let mut even_numbers = Vec::new();
    let mut index = 0;
    while index < arr.len()
        invariant
            index <= arr.len(),
            forall |x| #[trigger] arr.subrange(0, index).contains(x) && (x % 2 == 0) <==> even_numbers.contains(x),
    {
        if arr[index] % 2 == 0 {
            even_numbers.push(arr[index]);
        }
        index += 1;
        assert forall |x| #[trigger] arr.subrange(0, index).contains(x) && (x % 2 == 0) <==> even_numbers.contains(x);
    }
}

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    assert even_numbers_filter(*arr);
    assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
    while index < arr.len()
        invariant
            index <= arr.len(),
            forall |x| #[trigger] arr.subrange(0, index).contains(x) && (x % 2 == 0) <==> even_numbers.contains(x),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }
        index += 1;
        assert even_numbers_filter(arr);
        assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
    }
    assert even_numbers_filter(*arr);
    assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
    even_numbers
}

} // verus!


//     assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
//   assertion failed: even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False