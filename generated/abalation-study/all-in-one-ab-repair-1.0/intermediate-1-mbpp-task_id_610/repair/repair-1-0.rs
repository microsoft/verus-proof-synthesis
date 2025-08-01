
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 < k < list@.len(),
    ensures
        new_list@ == list@.subrange(0, k - 1 as int).add(
            list@.subrange(k as int, list.len() as int),
        ),
{
    let mut new_list = Vec::new();
    let mut index = 0;
    while index < k - 1
        invariant
            forall|i: int| 0 <= i < index ==> new_list@[i] == list@[i],
            forall|i: int| 0 <= i < list.len() ==> list@[i] == list@[i], // list is never changed in this loop
            index < k - 1,
            0 <= index <= k - 1,
            new_list.len() == index,
            new_list@.len() == index,
            list.len() > 0,
            0 < k < list@.len(),
    {
        new_list.push(list[index]);
        index += 1;
    }
    let mut index = k;
    while index < list.len()
        invariant
            forall|i: int| 0 <= i < k - 1 ==> new_list@[i] == list@[i],
            forall|i: int| 0 <= i < list.len() ==> list@[i] == list@[i], // list is never changed in this loop
            forall|i: int| k <= i < index ==> new_list@[i - 1] == list@[i],
            k <= index <= list.len(),
            new_list.len() == index - k,
            new_list@.len() == index - 1,
            list.len() > 0,
            0 < k < list@.len(),
    {
        new_list.push(list[index]);
        index += 1;
    }
    new_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpjlr5amib`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2
// Safe: False