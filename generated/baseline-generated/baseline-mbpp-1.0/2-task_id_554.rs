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
    assert(odd_numbers@ == arr@.take(0).filter(|x: u32| x % 2 != 0)); // initialization of invariant
    while index < arr.len()
        invariant
            0 <= index <= input_len,
            arr@.len() == input_len,
            odd_numbers@ == arr@.take(index as int).filter(|x: u32| x % 2 != 0),
    {
        if (arr[index] % 2 != 0) {
            odd_numbers.push(arr[index]);
        }
        assert(arr@.take(index as int + 1).drop_last() == arr@.take(index as int)); // maintain invariant
        index += 1;
    }
    assert(arr@ == arr@.take(arr.len() as int)); // for completeness
    odd_numbers
}

} // verus!
// Score: (1, 1)
// Safe: True