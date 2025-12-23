use vstd::prelude::*;

fn main() {}

verus! {

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_numbers: Vec<u32> = Vec::new();
    let mut index = 0;
    
    assert(even_numbers@ == arr@.take(0).filter(|x: u32| x % 2 == 0)); // ensuring initial empty state
    
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            even_numbers@ == arr@.take(index as int).filter(|x: u32| x % 2 == 0),
    {
        if arr[index] % 2 == 0 {
            even_numbers.push(arr[index]);
        }
        index += 1;
    }
    
    assert(arr@ == arr@.take(arr.len() as int)); // finalizer after completion of loop
    
    even_numbers
}

} // verus!
// Score: (1, 1)
// Safe: False