use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
{
    let mut new_list = Vec::new();
    let mut index = n;
    while index < list.len()
        invariant
            forall|i: int| n <= i < index ==> new_list[i - n] == list[i],
            index <= list.len(),
            n < list.len(),
            new_list.len() == index - n,
            0 < n,
            forall |k:int| 0 <= k < list.len() ==> list[k] == list[k], // list is not modified in this loop
    {
        new_list.push(list[index]);
        index += 1;
    }
    let mut index = 0;
    while index < n
        invariant
            forall|i: int| 0 <= i < index ==> new_list[list.len() - n + i] == list[i],
            index <= n,
            new_list.len() == list.len() - n + index,
            0 < n,
            forall |k:int| 0 <= k < list.len() ==> list[k] == list[k], // list is not modified in this loop
    {
        new_list.push(list[index]);
        index += 1;
    }
    proof {
        assert(new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)));
    }
    new_list
}

} // verus!

// failed this postcondition
//         new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
// at the end of the function body
// {
//     let mut new_list = Vec::new();
//     let mut index = n;
//     while index < list.len()
// ...
//     new_list
// }
//   at the end of the function body: {     let mut new_list = Vec::new();     let mut index = n;     while index < list.len()         invariant             forall|i: int| n <= i < index ==> new_list[i - n] == list[i],             index <= list.len(),             n < list.len(),             new_list.len() == index - n,             0 < n,             forall |k:int| 0 <= k < list.len() ==> list[k] == list[k], // list is not modified in this loop     {         new_list.push(list[index]);         index += 1;     }     let mut index = 0;     while index < n         invariant             forall|i: int| 0 <= i < index ==> new_list[list.len() - n + i] == list[i],             index <= n,             new_list.len() == list.len() - n + index,             0 < n,             forall |k:int| 0 <= k < list.len() ==> list[k] == list[k], // list is not modified in this loop     {         new_list.push(list[index]);         index += 1;     }     new_list }
//   failed this postcondition: new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int))

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True