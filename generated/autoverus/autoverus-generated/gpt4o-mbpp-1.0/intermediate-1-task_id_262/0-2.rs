use vstd::prelude::*;
fn main() {}

verus! {

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
            index <= l,
            part1@ == list@.subrange(0, index as int),
    {
        part1.push(list[index]);
        index += 1;
    }
    let mut part2: Vec<i32> = Vec::new();
    index = l;
    while index < list.len()
        invariant
            index <= list.len(),
            part2@ == list@.subrange(l as int, index as int),
    {
        part2.push(list[index]);
        index += 1;
    }
    (part1, part2)
}

} // verus!
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 5