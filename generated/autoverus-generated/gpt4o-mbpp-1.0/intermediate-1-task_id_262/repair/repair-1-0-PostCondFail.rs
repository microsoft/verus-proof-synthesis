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
            forall|k: int| 0 <= k < list.len() ==> list[k] == list[k], // list is never changed in the loop
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
            forall|k: int| 0 <= k < list.len() ==> list[k] == list[k], // list is never changed in the loop
            l <= index <= list.len(),
            part2.len() == index - l,
            0 < l < list@.len(), // invariant for l
    {
        part2.push(list[index]);
        index += 1;
    }
    proof {
        assert(list@.subrange(0, l as int).len() == l as int);
        assert(list@.subrange(l as int, list.len() as int).len() == (list.len() as int - l as int));
        assert(part1@ == list@.subrange(0, l as int));
        assert(part2@ == list@.subrange(l as int, list.len() as int));
    }
    (part1, part2)
}

} // verus!

// failed this postcondition
//         new_list.1@ == list@.subrange(l as int, list.len() as int),
// at the end of the function body
// {
//     let mut part1: Vec<i32> = Vec::new();
//     let mut index = 0;
//     while index < l
// ...
//     (part1, part2)
// }
//   at the end of the function body: {     let mut part1: Vec<i32> = Vec::new();     let mut index = 0;     while index < l         invariant             forall|j: int| 0 <= j < index ==> part1[j as int] == list[j as int],             forall|k: int| 0 <= k < list.len() ==> list[k] == list[k], // list is never changed in the loop             index <= l,             part1.len() == index,             0 < l < list@.len(), // invariant for l             // list.len() == list.len(), (Redundant invariant, removed for clarity)     {         part1.push(list[index]);         index += 1;     }     let mut part2: Vec<i32> = Vec::new();     index = l;     while index < list.len()         invariant             forall|j: int| l <= j < index ==> part2[(j - l) as int] == list[j as int],             forall|k: int| 0 <= k < list.len() ==> list[k] == list[k], // list is never changed in the loop             l <= index <= list.len(),             part2.len() == index - l,             0 < l < list@.len(), // invariant for l             // list.len() == list.len(), (Redundant invariant, removed for clarity)     {         part2.push(list[index]);         index += 1;     }     (part1, part2) }
//   failed this postcondition: new_list.1@ == list@.subrange(l as int, list.len() as int)

// Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True