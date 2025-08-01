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
        assert(rotation_split(list.len(), n) as int == split_index as int);
    }

    while index < list.len()
        invariant
            new_list.len() == (index - split_index),
            new_list@ == list@.subrange(split_index as int, index as int),
            0 <= split_index <= list.len(),
            split_index <= index <= list.len(),
    {
        new_list.push(list[index]);
        proof {
            assert(new_list@ == list@.subrange(split_index as int, index as int + 1));
        }
        index += 1;
    }

    index = 0;
    while index < split_index
        invariant
            new_list.len() == (list.len() - split_index + index),
            new_list@ == list@.subrange(split_index as int, list.len() as int).add(
                list@.subrange(0, index as int),
            ),
            0 <= index <= split_index <= list.len(),
    {
        new_list.push(list[index]);
        proof {
            assert(new_list@ == list@.subrange(split_index as int, list.len() as int).add(
                list@.subrange(0, index as int + 1),
            ));
        }
        index += 1;
    }
    
    new_list
}

} // verus!
// Score: (2, 2)
// Safe: True