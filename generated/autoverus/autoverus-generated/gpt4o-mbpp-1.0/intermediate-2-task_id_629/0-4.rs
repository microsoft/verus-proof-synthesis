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
            even_numbers.len() <= index,
            even_numbers@ == arr@[( 0..index ) as int].filter(|x: u32| x % 2 == 0),
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2