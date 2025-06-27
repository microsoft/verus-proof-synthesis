
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
        let mut index = split_index;

        // First while loop: Handling the first half after the rotation split
        while index < list.len()
            invariant
                forall|j: int| 0 <= j < (index - split_index) as int ==> new_list[j as usize] == list[(split_index + j as usize) % list.len()],
                index <= list.len(),
                new_list.len() == (index - split_index),
                new_list@ == list@.subrange(split_index as int, index as int),
                rotation_split(list.len(), n) == split_index as int,
                list.len() > 0,
        {
            new_list.push(list[index]);
            index += 1;
        }

        // Resetting index for the second part of the rotation
        index = 0;

        // Second while loop: Handling the second half before the rotation split
        while index < split_index
            invariant
                forall|j: int| 0 <= j < (list.len() - split_index + index) as int ==> new_list[j as usize] == list[(split_index + j as usize) % list.len()],
                index <= split_index,
                new_list.len() == (list.len() - split_index + index),
                new_list@ == list@.subrange(split_index as int, list.len() as int).add(list@.subrange(0, index as int)),
                rotation_split(list.len(), n) == split_index as int,
                list.len() > 0,
        {
            new_list.push(list[index]);
            index += 1;
        }

        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpl8gmh6g0`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: True