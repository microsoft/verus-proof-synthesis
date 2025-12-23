
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

        // First while-loop
        while index < list.len()
            invariant
                split_index <= index <= list.len(),
                new_list.len() == index - split_index,
                new_list@ == list@.subrange(split_index as int, index as int),
        {
            new_list.push(list[index]);
            index += 1;
        }

        index = 0;

        // Second while-loop
        while index < split_index
            invariant
                0 <= index <= split_index,
                new_list.len() == list.len() - split_index + index,
                new_list@ == list@.subrange(split_index as int, list.len() as int).add(list@.subrange(0, index as int)),
        {
            new_list.push(list[index]);
            index += 1;
        }

        // Post-condition proof block
        proof {
            assert(new_list.len() == list.len());
            assert(new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int)
                .add(list@.subrange(0, rotation_split(list.len(), n) as int)));
        }

        new_list
    }
}

// Score: (0, 5)
// Safe: True