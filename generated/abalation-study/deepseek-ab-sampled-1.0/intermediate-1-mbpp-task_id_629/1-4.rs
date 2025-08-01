
use vstd::prelude::*;

fn main() {}

verus! {

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;

    assert(even_numbers@ =~= Seq::empty());

    // First, ensure that even_numbers is empty before starting
    while index < arr.len() {
        invariant
            index <= arr.len(),
            even_numbers@ == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0),
            even_numbers@.len() == arr@.subrange(0, index as int).filter(|x: u32| x % 2 == 0).len()
        {
            if (arr[index] % 2 == 0) {
                even_numbers.push(arr[index]);
            }
            index += 1;
        }
    }

    // Ensure that the loop has processed the entire array
    assert(index == arr.len());
    assert(even_numbers@ =~= arr@.filter(|x: u32| x % 2 == 0));

    even_numbers
}

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1