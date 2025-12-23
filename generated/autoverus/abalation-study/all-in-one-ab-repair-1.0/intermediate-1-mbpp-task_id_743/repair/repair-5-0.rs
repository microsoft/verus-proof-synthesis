
use vstd::prelude::*;
fn main() {}

verus! {
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
        
        proof {
            assert(rotation_split(list.len(), n) == split_index as int);
            assert(split_index <= list.len());
        }

        while index < list.len()
            invariant
                split_index <= index <= list.len(),
                new_list.len() == index - split_index,
                forall|j: int| 
                    0 <= j < (index - split_index) as int ==> new_list[j as usize] == list[(split_index + j as usize)],
                rotation_split(list.len(), n) == split_index as int,
                list.len() > 0,
        {
            new_list.push(list[index]);
            index += 1;
        }

        index = 0;

        while index < split_index
            invariant
                0 <= index <= split_index,
                new_list.len() == (list.len() - split_index) + index,
                forall|j: int|
                    0 <= j < new_list.len() ==> 
                        if j < (list.len() - split_index) as int {
                            new_list[j as usize] == list[split_index + j as usize]
                        } else {
                            new_list[j as usize] == list[j as usize - (list.len() - split_index)]
                        },
                rotation_split(list.len(), n) == split_index as int,
                list.len() > 0,
        {
            new_list.push(list[index]);
            index += 1;
        }

        new_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp8rjhsu7o`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: True