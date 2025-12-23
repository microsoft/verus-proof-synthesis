
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    spec fn rotation_split(len: usize, n: usize) -> int {
        len as int - (n as int % len as int)
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
                forall|j: int| 0 <= j < new_list.len() as int ==> new_list[j as usize] == list[(split_index + j as usize) % list.len()],
                index <= list.len(),
                new_list.len() as int == index as int - split_index as int,
                new_list@ == list@.subrange(split_index as int, index as int),
                rotation_split(list.len(), n) == split_index as int,
                list.len() > 0,
                list.len() == list.len(), // Loop invariant for list length
        {
            new_list.push(list[index]);
            index += 1;
        }

        index = 0;
        while index < split_index
            invariant
                forall|j: int| 0 <= j < new_list.len() as int ==> (
                    j < (list.len() - split_index) as int &&
                    new_list[j as usize] == list[(split_index + j as usize) % list.len()] ||
                    j >= (list.len() - split_index) as int &&
                    new_list[j as usize] == list[j - (list.len() as int - split_index as int)]
                ),
                index <= split_index,
                new_list.len() as int == (list.len() - split_index) as int + index as int,
                new_list@ == list@.subrange(split_index as int, list.len() as int).add(
                    list@.subrange(0, index as int),
                ),
                rotation_split(list.len(), n) == split_index as int,
                list.len() > 0,
                list.len() == list.len(), // Loop invariant for list length
        {
            new_list.push(list[index]);
            index += 1;
        }
        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpaq1nlb7y`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: True