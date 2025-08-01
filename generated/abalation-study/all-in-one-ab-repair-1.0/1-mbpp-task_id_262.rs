
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn split_array(list: &Vec<i32>, l: usize) -> (new_list: (Vec<i32>, Vec<i32>))
    requires
        list@.len() > 0,
        0 < l < list@.len(),
    ensures
        new_list.0@ == list@.subrange(0, l as int),
        new_list.1@ == list@.subrange(l as int, list.len() as int),
{
    let mut part1: Vec<i32> = Vec::new();
    let mut index = 0;
    while index < l
        invariant
            forall|j: int| 0 <= j < index ==> part1[j as int] == list[j as int],
            index <= l,
            part1.len() == index,
            0 < l < list@.len(), // invariant for l
    {
        part1.push(list[index]);
        index += 1;
    }
    let mut part2: Vec<i32> = Vec::new();
    index = l;
    while index < list.len()
        invariant
            forall|j: int| l <= j < index ==> part2[(j - l) as int] == list[j as int],
            l <= index <= list.len(),
            part2.len() == (index - l),
            0 < l < list@.len(), // invariant for l
    {
        part2.push(list[index]);
        index += 1;
    }
    
    proof {
        // Invariants ensure that the split parts are correctly assigned
        assert(forall|j: int| 0 <= j < part1.len() ==> part1[j] == list[j]);
        assert(forall|j: int| 0 <= j < part2.len() ==> part2[j] == list[j + l]);
        
        assert(part1@ == list@.subrange(0, l as int));
        assert(part2@ == list@.subrange(l as int, list.len() as int));
    }
    (part1, part2)
}

} // verus!

// Score: (1, 0)
// Safe: True