use vstd::prelude::*;
fn main() {}
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
            forall|i: int|
                0 <= i < new_list.len() ==> new_list[i] == list[(split_index + i) % (
                list.len()) as int],
            forall|j: int|
                0 <= j < new_list.len() ==> new_list[j] == list[(split_index + j) as int],
            index <= list.len(),
            new_list.len() <= list.len(),
            new_list.len() == (list.len() - split_index) - (list.len() - index),
            new_list.len() == index - split_index,
            new_list@ == list@.subrange(split_index as int, index as int),
            rotation_split(list.len(), n) == split_index as int,
    {
        new_list.push(list[index]);
        index += 1;
    }
    index = 0;
    while index < split_index
        invariant
            forall|i: int|
                (list.len() - split_index) <= i < new_list.len() ==> new_list[i] == list[i - (
                list.len() - split_index)],
            forall|i: int|
                0 <= i < (list.len() - split_index) ==> new_list[i] == list[(split_index + i) % (
                list.len()) as int],
            forall|j: int|
                0 <= j < list.len() - split_index + index ==> new_list[j] == if j < list.len()
                    - split_index {
                    list[split_index + j]
                } else {
                    list[(j - (list.len() - split_index)) as int]
                },
            index <= split_index,
            new_list.len() <= list.len(),
            new_list.len() == (list.len() - split_index) + index,
            new_list.len() == list.len() - split_index + index,
            new_list@.len() == (list.len() as int) - (split_index as int) + (index as int),
            new_list@ == list@.subrange(split_index as int, list.len() as int).add(
                list@.subrange(0, index as int),
            ),
            new_list@ == list@.subrange(split_index as int, list.len() as int).add(
                list@.subrange(0, index as int),
            ),
            new_list@ == list@.subrange(split_index as int, list.len() as int).add(
                list@.subrange(0, index as int),
            ),
            rotation_split(list.len(), n) == split_index as int,
    {
        new_list.push(list[index]);
        index += 1;
    }
    new_list
}

} // verus!


// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 9