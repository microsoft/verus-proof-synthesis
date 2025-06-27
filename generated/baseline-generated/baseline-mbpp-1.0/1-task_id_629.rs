use vstd::prelude::*;

fn main() {}

verus! {

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;

    assert(even_numbers@ == arr@.take(0).filter(|x: u32| x % 2 == 0)); // Initial assertion

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            even_numbers@ == arr@.take(index as int).filter(|x: u32| x % 2 == 0), // Loop invariant
    {
        if arr[index] % 2 == 0 {
            even_numbers.push(arr[index]);
        }

        assert(arr@.take((index + 1) as int).drop_last() == arr@.take(index as int)); // Routine assertion
        reveal(Seq::filter); // Revealing the filter specification

        index += 1;
    }

    assert(arr@ == arr@.take(arr.len() as int)); // Final assertion
    even_numbers
}

} // verus!
// Score: (2, 0)
// Safe: False