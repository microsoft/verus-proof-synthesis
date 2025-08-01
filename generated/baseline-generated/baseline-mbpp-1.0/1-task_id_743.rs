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

    proof {
        // Prove that split_index is within bounds
        assert(0 <= split_index <= list.len());
    }

    while index < list.len()
        invariant
            0 <= index <= list.len(),
            new_list.len() == index - split_index,
            forall |k: int| 0 <= k < new_list.len() ==> new_list[k] == list[split_index + k],
    {
        new_list.push(list[index]);
        index += 1;
    }

    index = 0;

    while index < split_index
        invariant
            0 <= index <= split_index,
            new_list.len() == list.len() - split_index + index,
            forall |k: int| 0 <= k < list.len() - split_index ==> new_list[k] == list[split_index + k],
            forall |k: int| 0 <= k < index ==> new_list[list.len() - split_index + k] == list[k],
    {
        new_list.push(list[index]);
        index += 1;
    }

    new_list
}

} // verus!
// Score: (1, 3)
// Safe: True