
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
            assert(rotation_split(list.len(), n) == split_index as int);
            assert(split_index <= list.len());
        }

        while index < list.len()
            invariant
                0 <= split_index <= list.len(),
                0 <= index <= list.len(),
                split_index <= index <= list.len(),
                new_list.len() <= list.len(),
                forall|j: int| 
                    0 <= j < (index - split_index) as int ==> new_list[j as usize] == list[split_index + j as usize],
                forall|k: int| 0 <= k < list.len() ==> list[k] == list[k], // list is never changed in the loop
                new_list@ == list@.subrange(split_index as int, index as int),
                rotation_split(list.len(), n) == split_index as int,
                list.len() > 0,
        {
            new_list.push(list[index]);
            index += 1;
        }

        index = 0;

        while index < split_index
            invariant
                0 <= split_index <= list.len(),
                0 <= index <= split_index,
                split_index <= list.len(),
                new_list.len() <= list.len(),
                forall|j: int| 
                    0 <= j < (list.len() - split_index) as int ==> new_list[j as usize] == list[split_index + j as usize],
                forall|j: int|
                    (list.len() - split_index) <= j < (list.len() - split_index) + index as int ==>
                        new_list[j as usize] == list[j - (list.len() - split_index)],
                forall|k: int| 0 <= k < list.len() ==> list[k] == list[k], // list is never changed in the loop
                new_list@ == list@.subrange(split_index as int, list.len() as int).add(
                    list@.subrange(0, index as int)),
                rotation_split(list.len(), n) == split_index as int,
                list.len() > 0,
        {
            new_list.push(list[index]);
            index += 1;
        }

        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpgvq_rbat`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: True