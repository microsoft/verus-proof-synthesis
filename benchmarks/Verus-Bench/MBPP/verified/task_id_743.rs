use vstd::prelude::*;
fn main() {
    //Write a method in Rust to rotate a given list by specified N number of items to the right direction.

    assert_eq!(
        rotate_right(&vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 3),
        [8, 9, 10, 1, 2, 3, 4, 5, 6, 7]
    );
    assert_eq!(
        rotate_right(&vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 2),
        [9, 10, 1, 2, 3, 4, 5, 6, 7, 8]
    );
    assert_eq!(
        rotate_right(&vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 5),
        [6, 7, 8, 9, 10, 1, 2, 3, 4, 5]
    );
}

verus! {

spec fn rotation_split(len: usize, n: usize) -> int {
    len - (n % len)
}

fn rotate_right(list: &Vec<u32>, n: usize) -> (new_list: Vec<u32>)
    requires
        list.len() > 0,
    ensures
        new_list.len() == list.len(),
        new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int).add(
            list@.subrange(0, rotation_split(list.len(), n) as int),
        ),
{
    let rotation = n % list.len();
    let split_index = list.len() - rotation;

    let mut new_list = Vec::with_capacity(list.len());

    let mut index = split_index;

    while index < list.len()
        invariant
            split_index <= index <= list.len(),
            list@.subrange(split_index as int, index as int) =~= new_list@,
    {
        new_list.push(list[index]);
        index += 1;
    }
    index = 0;
    while index < split_index
        invariant
            0 <= split_index <= list@.len(),
            0 <= index <= split_index,
            new_list@ =~= list@.subrange(split_index as int, list@.len() as int).add(
                list@.subrange(0, index as int),
            ),
    {
        new_list.push(list[index]);
        index += 1;
    }
    assert(new_list@ =~= list@.subrange(split_index as int, list@.len() as int).add(
        list@.subrange(0, split_index as int),
    ));
    new_list
}

} // verus!
