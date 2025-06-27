
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
    let n = arr.len();
    while index < n
        invariant
            even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
            index <= n,
            n == arr.len(), // ensure that n is equal to the initial length
            forall |k:int| 0 <= k < n ==> arr[k] == arr@[k], // ensure arr is not modified
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
            assert(even_numbers@ == arr@.subrange(0, index as int + 1).filter(|x: u32| x % 2 == 0));
        } else {
            assert(even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0));
        }
        index += 1;
    }
    even_numbers
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpekiu3j21`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4
// Safe: False