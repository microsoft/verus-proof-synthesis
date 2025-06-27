
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
            assert(0 <= split_index <= list.len());
        }

        while index < list.len()
            invariant
                0 <= split_index <= list.len(),
                0 <= index <= list.len(),
                n == list.len() && new_list.len() == index - split_index as usize,
                new_list@ == list@.subrange(split_index as int, index as int),
        {
            new_list.push(list[index]);
            index += 1;
        }

        index = 0;

        while index < split_index
            invariant
                0 <= split_index <= list.len(),
                0 <= index < split_index,
                n == list.len() && new_list.len() == (list.len() - split_index) + index,
                new_list@ == list@.subrange(split_index as int, list.len() as int).add(
                    list@.subrange(0, index as int)
                ),
        {
            new_list.push(list[index]);
            index += 1;
        }

        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmppnwm8pfq`)
// 

// Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 6
// Safe: True