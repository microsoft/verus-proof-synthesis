
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

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
    let mut index = 0;

    // First loop to add elements starting from the split_index
    while index < list.len() - split_index
        invariant
            new_list.len() == index,
            new_list@ == list@.subrange(split_index as int, (split_index + index) as int),
            index <= list.len() - split_index,
            forall|j: int| 0 <= j < index ==> new_list[j] == list[(split_index + j) as int],
            list.len() > 0,
            list.len() == list.len(),
            rotation_split(list.len(), n) == split_index as int,
    {
        new_list.push(list[split_index + index]);
        index += 1;
    }

    // Second loop to add elements from 0 to split_index
    index = 0;
    while index < split_index
        invariant
            new_list.len() == (list.len() - split_index) + index,
            new_list@ == list@.subrange(split_index as int, list.len() as int).add(list@.subrange(0, index as int)),
            index <= split_index,
            forall|j: int| 0 <= j < index ==> new_list[(list.len() - split_index + j) as int] == list[j as int],
            list.len() > 0,
            list.len() == list.len(),
            rotation_split(list.len(), n) == split_index as int,
    {
        new_list.push(list[index]);
        index += 1;
    }

    new_list
}

} // verus!



// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmps9ks2elu`)
// 

// Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 4
// Safe: False