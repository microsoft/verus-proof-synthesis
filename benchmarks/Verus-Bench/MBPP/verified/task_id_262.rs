use vstd::prelude::*;
fn main() {
    /*Write a function in Rust that takes in a list and an integer L and splits the given list into two parts
    where the length of the first part of the list is L, and returns the resulting lists in a tuple*/

    assert_eq!(
        split_array(&vec![1, 1, 2, 3, 4, 4, 5, 1], 3),
        (vec![1, 1, 2], vec![3, 4, 4, 5, 1])
    );
    assert_eq!(
        split_array(&vec![1, 1, 2, 3, 4, 4, 5, 1], 4),
        (vec![1, 1, 2, 3], vec![4, 4, 5, 1])
    );
    assert_eq!(
        split_array(&vec![1, 1, 2, 3, 4, 4, 5, 1], 2),
        (vec![1, 1], vec![2, 3, 4, 4, 5, 1])
    );
}

verus! {

fn split_array(list: &Vec<i32>, l: usize) -> (new_list: (Vec<i32>, Vec<i32>))
    requires
        list@.len() > 0,
        0 < l < list@.len(),
    ensures
        new_list.0@ == list@.subrange(0, l as int),
        new_list.1@ == list@.subrange(l as int, list.len() as int),
{
    let mut part1: Vec<i32> = Vec::new();
    let mut index = 0;
    while index < l
        invariant
            0 < l < list@.len(),
            0 <= index <= l,
            part1@ =~= list@.subrange(0, index as int),
    {
        part1.push(list[index]);
        index += 1;
    }
    let mut part2: Vec<i32> = Vec::new();
    index = l;
    while index < list.len()
        invariant
            l <= index <= list.len(),
            part2@ =~= list@.subrange(l as int, index as int),
    {
        part2.push(list[index]);
        index += 1;
    }

    (part1, part2)
}

} // verus!
