
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

proof fn filter_even_numbers(arr: &Vec<u32>, even_numbers: &Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    assert(even_numbers@ == Vec::empty());
    let mut index = 0;
    while index < arr.len()
        invariant
            index <= arr.len(),
            forall |i| 0 <= i <= index ==> (arr@[i] % 2 == 0 <==> even_numbers@.contains(arr@[i])),
    {
        if (arr[index] % 2 == 0) {
            assert(even_numbers@.contains(arr@[index]));
        } else {
            assert(!even_numbers@.contains(arr@[index]));
        }
        index += 1;
    }
    forall |x| even_numbers@.contains(x) <==> arr@.filter(|n: u32| n % 2 == 0).contains(x);
}

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    proof {
        let mut even_numbers: Vec<u32> = Vec::empty();
        filter_even_numbers(arr, &even_numbers);
    }

    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    while index < arr.len()
        invariant
            index <= arr.len(),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }
        index += 1;
    }
    even_numbers
}

} // verus!


//     assert(even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)); // Added by AI
//   assertion failed: even_numbers@ == arr@.filter(|x: u32| x % 2 == 0)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True