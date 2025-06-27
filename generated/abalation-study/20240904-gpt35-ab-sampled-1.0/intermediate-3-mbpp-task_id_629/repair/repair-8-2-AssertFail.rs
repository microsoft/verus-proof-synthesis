
use vstd::prelude::*;
fn main() {}

verus! {

/// Helper function to prove that every element in the resulting vector satisfies the predicate
proof fn filter_predicate_preserved(pred: &fun(u32) -> bool, arr: &Vec<u32>, res: &Vec<u32>)
    requires forall |i| 0 <= i < arr.len() ==> pred(arr[i]) <==> res.contains(arr[i]),
{
    var i: uSize = 0;
    while i < arr.len()
        invariant 0 <= i <= arr.len(),
        forall |j| 0 <= j < i ==> pred(arr[j]) <==> res.contains(arr[j]),
    {
        if pred(arr[i]) {
            assert(res.contains(arr[i]));
        } else {
            assert(!res.contains(arr[i]));
        }
        i += 1;
    }
}

# [verifier::loop_isolation(false)]
fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
    while index < arr.len()
        invariant
            index <= arr.len(),
            filter_predicate_preserved(&(|x: u32| x % 2 == 0), arr, &even_numbers),
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


//     assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
//   assertion failed: even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False