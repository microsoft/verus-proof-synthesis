
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
        
        while index < list.len()
            invariant
                index <= list.len(),
                new_list.len() == index - split_index,
                new_list@ == list@.subrange(split_index as int, index as int),
        {
            new_list.push(list[index]);
            index += 1;
        }
        
        index = 0;

        while index < split_index
            invariant
                index <= split_index,
                new_list.len() == list.len() - split_index + index,
                new_list@ == list@.subrange(split_index as int, list.len() as int).add(list@.subrange(0, index as int)),
        {
            new_list.push(list[index]);
            index += 1;
        }
        
        // Proof block for ensuring postconditions
        proof {
            assert(new_list.len() == list.len());
            assert(new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int)
                .add(list@.subrange(0, rotation_split(list.len(), n) as int)));
        }
        
        new_list
    }
}

If you continue to experience the filename error, ensure the Verus tool is being called correctly. You should specify the filename of the Rust source code you want to verify as an argument to the Verus command.

For example:

sh
verus your_filename.rs


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp894_8aub`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False