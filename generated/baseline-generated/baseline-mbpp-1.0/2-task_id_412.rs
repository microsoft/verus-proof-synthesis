use vstd::prelude::*;

fn main() {}

verus! {

fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut even_list: Vec<u32> = Vec::new();
    let input_len = arr.len();

    let mut index = 0;
    assert(even_list@ == arr@.take(0).filter(|x: u32| x % 2 == 0)); // Initial state before loop

    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            arr@.len() == input_len,
            even_list@ == arr@.take(index as int).filter(|x: u32| x % 2 == 0), // maintaining the filter property
    {
        if arr[index] % 2 == 0 {
            even_list.push(arr[index]);
        }
        assert(arr@.take(index as int + 1).drop_last() == arr@.take(index as int)); // property before the operation
        reveal(Seq::filter); // to reveal the filter property
        index += 1;
    }

    assert(arr@ == arr@.take(input_len as int)); // maintaining the input length property
    even_list
}

} // verus!
// Score: (2, 0)
// Safe: False