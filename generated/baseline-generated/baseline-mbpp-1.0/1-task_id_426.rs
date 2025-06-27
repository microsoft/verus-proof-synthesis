use vstd::prelude::*;

fn main() {}

verus! {

fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut odd_list: Vec<u32> = Vec::new();
    let input_len = arr.len();

    let mut index = 0;

    assert(odd_list@ == arr@.take(0).filter(|x: u32| x % 2 != 0)); // Added by AI
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            arr@.len() == input_len,  // Always specify the length of vectors used in the loop
            odd_list@ == arr@.take(index as int).filter(|x: u32| x % 2 != 0), // Routine for filter
    {
        if (arr[index] % 2 != 0) {
            odd_list.push(arr[index]);
        }
        assert(arr@.take((index + 1) as int).drop_last() == arr@.take(index as int)); // Routine for take and filter
        reveal(Seq::filter); // Routine for filter
        index += 1;
    }
    assert(arr@ == arr@.take(arr.len() as int)); // Routine for take
    odd_list
}

} // verus!
// Score: (2, 0)
// Safe: True