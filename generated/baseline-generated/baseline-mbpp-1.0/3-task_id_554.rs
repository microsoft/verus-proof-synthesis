use vstd::prelude::*;

fn main() {}

verus! {

fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut odd_numbers: Vec<u32> = Vec::new();
    let input_len = arr.len();

    let mut index = 0;
    assert(odd_numbers@ == arr@.take(0).filter(|x: u32| x % 2 != 0)); // Added by AI
    
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            odd_numbers@ == arr@.take(index as int).filter(|x: u32| x % 2 != 0),
            arr@.len() == input_len, // Added by AI
    {
        proof {
            assert(arr@.take((index + 1) as int).drop_last() == arr@.take(index as int)); // Added by AI
            reveal(Seq::filter); // Added by AI
        }
        if arr[index] % 2 != 0 {
            odd_numbers.push(arr[index]);
        }
        index += 1;
    }

    assert(arr@ == arr@.take(arr.len() as int)); // Added by AI
    odd_numbers
}

} // verus!
// Score: (2, 0)
// Safe: False