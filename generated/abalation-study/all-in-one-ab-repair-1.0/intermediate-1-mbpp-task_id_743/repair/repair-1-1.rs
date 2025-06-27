
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
                index <= list.len(),
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
                index <= split_index,
                new_list.len() == list.len() - split_index + index,
                new_list@ == list@.subrange(split_index as int, list.len() as int).add(
                    list@.subrange(0, index as int) 
                ),
                rotation_split(list.len(), n) == split_index as int,
        {
            new_list.push(list[index]);
            index += 1;
        }

        // Ensure the list hasn't been modified
        proof {
            // This section uses a ghost variable to ensure that the list remains unchanged
            let original_list = list@;
            assert(forall|k: int| 0 <= k < list.len() ==> list[k] == original_list[k]);
        }
        
        new_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpaydvc96j`)
// 

// Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 4
// Safe: True