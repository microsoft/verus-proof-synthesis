use vstd::prelude::*;

fn main() {
    // Write a function in Rust to remove duplicate numbers from a given list.

    assert_eq!(remove_duplicates(&vec![1, 2, 3, 2, 3, 4, 5]), [1, 4, 5]);
    assert_eq!(remove_duplicates(&vec![1, 2, 3, 2, 4, 5]), [1, 3, 4, 5]);
    assert_eq!(remove_duplicates(&vec![1, 2, 3, 4, 5]), [1, 2, 3, 4, 5]);
}

verus! {

pub open spec fn count_frequency_rcr(seq: Seq<i32>, key: i32) -> int
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_frequency_rcr(seq.drop_last(), key) + if (seq.last() == key) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_frequency(arr: &Vec<i32>, key: i32) -> (frequency: usize)
    ensures
        count_frequency_rcr(arr@, key) == frequency,
{
    let mut index = 0;
    let mut counter = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            0 <= counter <= index,
            count_frequency_rcr(arr@.subrange(0, index as int), key) == counter,
    {
        if (arr[index] == key) {
            counter += 1;
        }
        index += 1;
        assert(arr@.subrange(0, index - 1 as int) == arr@.subrange(0, index as int).drop_last());
    }
    assert(arr@ == arr@.subrange(0, index as int));
    counter
}

fn remove_duplicates(arr: &Vec<i32>) -> (unique_arr: Vec<i32>)
    ensures
        unique_arr@ == arr@.filter(|x: i32| count_frequency_rcr(arr@, x) == 1),
{
    let mut unique_arr: Vec<i32> = Vec::new();
    let input_len = arr.len();

    assert(arr@.take(0int).filter(|x: i32| count_frequency_rcr(arr@, x) == 1) == Seq::<
        i32,
    >::empty());

    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            unique_arr@ == arr@.take(index as int).filter(
                |x: i32| count_frequency_rcr(arr@, x) == 1,
            ),
    {
        if count_frequency(&arr, arr[index]) == 1 {
            unique_arr.push(arr[index]);
        }
        assert(arr@.take((index + 1) as int).drop_last() == arr@.take(index as int));
        reveal(Seq::filter);
        index += 1;
    }
    assert(arr@ == arr@.take(input_len as int));
    unique_arr
}

} // verus!
