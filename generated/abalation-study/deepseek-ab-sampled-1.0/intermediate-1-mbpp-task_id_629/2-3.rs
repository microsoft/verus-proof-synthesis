

use vstd::prelude::*;

fn main() {}

verus! {

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    requires
        arr@.len() == old(arr).len(),
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    while index < arr.len()
        invariant 
            index <= arr.len(),
            even_numbers.len() == index - arr@.count(|x: u32| x % 2 != 0),
            arr@.count(|x: u32| x % 2 != 0 && x < 2^(32-1)) == arr.len() - even_numbers.len(),
            even_numbers@ == arr@.subrange(0, index).filter(|x: u32| x % 2 == 0),
    {
        let current_element = arr[index];
        if (current_element % 2 == 0) {
            even_numbers.push(current_element);
        }
        index += 1;
    }
    even_numbers
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4