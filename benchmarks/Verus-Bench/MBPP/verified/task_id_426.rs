use vstd::prelude::*;

fn main() {
    // Write a function in Rust to filter odd numbers.

    assert_eq!(
        filter_odd_numbers(&vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]),
        [1, 3, 5, 7, 9]
    );
    assert_eq!(
        filter_odd_numbers(&vec![10, 20, 45, 67, 84, 93]),
        [45, 67, 93]
    );
    assert_eq!(filter_odd_numbers(&vec![5, 7, 9, 8, 6, 4, 3]), [5, 7, 9, 3]);
}

verus! {

fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut odd_list: Vec<u32> = Vec::new();
    let input_len = arr.len();

    assert(arr@.take(0int).filter(|x: u32| x % 2 != 0) == Seq::<u32>::empty());
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            odd_list@ == arr@.take(index as int).filter(|x: u32| x % 2 != 0),
    {
        if (arr[index] % 2 != 0) {
            odd_list.push(arr[index]);
        }
        assert(arr@.take((index + 1) as int).drop_last() == arr@.take(index as int));
        reveal(Seq::filter);
        index += 1;
    }
    assert(arr@ == arr@.take(input_len as int));
    odd_list
}

} // verus!
