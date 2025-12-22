use vstd::prelude::*;

fn main() {
    // Write a function in Rust to find the first odd number in a given list of numbers.

    assert_eq!(find_first_odd(&vec![]), None);
    assert_eq!(find_first_odd(&vec![2, 4, 6, 8]), None);
    assert_eq!(find_first_odd(&vec![1, 3, 5]), Some(0));
    assert_eq!(find_first_odd(&vec![8, 9, 1]), Some(1));
    assert_eq!(find_first_odd(&vec![2, 4, 1, 3]), Some(2));
}

verus! {

fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    ensures
        if let Some(idx) = index {
            &&& arr@.take(idx as int) == arr@.take(idx as int).filter(|x: u32| x % 2 == 0)
            &&& arr[idx as int] % 2 != 0
        } else {
            forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
        },
{
    let input_len = arr.len();
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            arr@.take(index as int) =~= arr@.take(index as int).filter(|x: u32| x % 2 == 0),
    {
        if (arr[index] % 2 != 0) {
            return Some(index);
        }
        assert(arr@.take((index + 1) as int).drop_last() == arr@.take(index as int));
        reveal(Seq::filter);
        index += 1;
    }
    assert(arr@ == arr@.take(input_len as int));
    None
}

} // verus!
