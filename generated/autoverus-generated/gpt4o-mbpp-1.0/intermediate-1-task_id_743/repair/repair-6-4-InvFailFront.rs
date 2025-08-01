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
    proof {
        assert(new_list@ == list@.subrange(split_index as int, split_index as int)); // Added by AI
    }
    while index < list.len()
        invariant
            forall|j: int|
                0 <= j < new_list.len() ==> new_list[j] == list[(split_index + j) as int],
            forall|k: int| 0 <= k < list.len() ==> list[k] == list[k], // list is never changed in the loop
            index <= list.len(),
            new_list.len() == index - split_index,
            new_list@ == list@.subrange(split_index as int, index as int),
            rotation_split(list.len(), n) == split_index as int,
            list.len() > 0,
            list.len() == list.len(), // Loop invariant for list length
    {
        new_list.push(list[index]);
        index += 1;
    }
    index = 0;
    proof {
        assert(new_list@ == list@.subrange(split_index as int, list@.len() as int).add(list@.subrange(0, index as int))); // Added by AI
    }
    while index < split_index
        invariant
            forall|j: int|
                0 <= j < list.len() - split_index + index ==> new_list[j] == if j < list.len()
                    - split_index {
                    list[split_index + j]
                } else {
                    list[(j - (list.len() - split_index)) as int]
                },
            forall|k: int| 0 <= k < list.len() ==> list[k] == list[k], // list is never changed in the loop
            index <= split_index,
            new_list.len() == list.len() - split_index + index,
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

} // verus!

//             new_list@ == list@.subrange(split_index as int, list.len() as int).add(
//                 list@.subrange(0, index as int),
//             ),
//   None: new_list@ == list@.subrange(split_index as int, list.len() as int).add(                 list@.subrange(0, index as int),             )

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True