
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
        
        // Loop to handle the second part of the rotation
        while index < list.len()
            invariant
                index <= list.len(),
                new_list.len() == index - split_index,
                new_list@ == list@.subrange(split_index as int, index as int),
        {
            proof {
                assert(index - split_index <= list.len());
                assert(list@.subrange(split_index as int, index as int).len() == index - split_index);
            }
            new_list.push(list[index]);
            index += 1;
        }
        
        index = 0;
        
        // Loop to handle the first part of the rotation
        while index < split_index
            invariant
                index <= split_index,
                new_list.len() == list.len() - split_index + index,
                new_list@ == list@.subrange(split_index as int, list.len() as int).add(list@.subrange(0, index as int)),
        {
            proof {
                assert(new_list.len() == index + (list.len() - split_index));
                assert(list@.subrange(split_index as int, list.len() as int).len() == list.len() - split_index);
                assert(list@.subrange(0, index as int).len() == index);
            }
            new_list.push(list[index]);
            index += 1;
        }
        
        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp39uv6hhx`)
// 

// Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 5
// Safe: True