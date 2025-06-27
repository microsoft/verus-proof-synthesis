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
        // Proof that after the first loop new_list contains the correct elements
        assert(0 <= split_index < list.len() + 1);
        assert(new_list.len() == 0);
    }

    while index < list.len()
        invariant
            split_index as int == rotation_split(list.len(), n),
            0 <= split_index <= list.len(),
            split_index <= index <= list.len(),
            new_list@ == list@.subrange(split_index as int, index as int),
    {
        new_list.push(list[index]);
        index += 1;

        proof {
            assert(new_list.len() == (index - split_index));
            assert(new_list@ == list@.subrange(split_index as int, index as int));
        }
    }

    index = 0;

    while index < split_index 
        invariant
            split_index as int == rotation_split(list.len(), n),
            0 <= split_index <= list.len(),
            0 <= index <= split_index,
            new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int).add(list@.subrange(0, index as int)),
    {
        new_list.push(list[index]);
        index += 1;

        proof {
            assert(new_list.len() == (list.len() - split_index + index));
            assert(new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int).add(list@.subrange(0, index as int)));
        }
    }

    proof {
        assert(new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int).add(list@.subrange(0, rotation_split(list.len(), n) as int)));
    }

    new_list
}

} // verus!
// Score: (2, 2)
// Safe: True