
use vstd::prelude::*;

fn main() {}

verus! {

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    while index < arr.len()
        invariant
            index <= arr.len(),
            even_numbers@ == arr@.filter(|x: u32| x % 2 == 0).subrange(0, index as int),
    {
        if (arr[index] % 2 == 0) {
            even_numbers.push(arr[index]);
        }
        index += 1;
    }
    even_numbers
}

} // verus!

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3