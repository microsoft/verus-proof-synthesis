use vstd::prelude::*;

fn main() {
    // Write a function in Rust which takes a list of integers and only returns the odd ones.

    assert_eq!(find_odd_numbers(&vec![1, 2, 3, 4, 5, 6]), [1, 3, 5]);
    assert_eq!(find_odd_numbers(&vec![10, 11, 12, 13]), [11, 13]);
    assert_eq!(find_odd_numbers(&vec![7, 8, 9, 1]), [7, 9, 1]);
}

verus! {

fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut odd_numbers: Vec<u32> = Vec::new();
    let input_len = arr.len();

    assert(arr@.take(0int).filter(|x: u32| x % 2 != 0) == Seq::<u32>::empty());
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            odd_numbers@ == arr@.take(index as int).filter(|x: u32| x % 2 != 0),
    {
        if (arr[index] % 2 != 0) {
            odd_numbers.push(arr[index]);
        }
        assert(arr@.take((index + 1) as int).drop_last() == arr@.take(index as int));
        reveal(Seq::filter);
        index += 1;
    }
    assert(arr@ == arr@.take(input_len as int));
    odd_numbers
}

} // verus!
