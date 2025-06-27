
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]
fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 <= k < list@.len(),
    ensures
        new_list@ == list@.subrange(0, k as int).add(
            list@.subrange(k as int + 1, list.len() as int)
        ),
{
    let mut new_list = Vec::new();
    let mut index = 0;
    while index < k
        invariant
            list.len() > 0,
            0 <= k < list@.len(),
            index <= k,
            new_list.len() == index,
            new_list@ == list@.subrange(0, index as int),
    {
        new_list.push(list[index]);
        index += 1;
    }
    index += 1; // skip the k-th element
    while index < list.len()
        invariant
            list.len() > 0,
            0 <= k < list@.len(),
            k < list.len(), // this is ensured by k < list@.len() and list.len() > 0
            index <= list.len(),
            new_list.len() == index - 1,
            new_list@ == list@.subrange(0, k as int).add(list@.subrange(k as int + 1, index as int)),
    {
        new_list.push(list[index]);
        index += 1;
    }
    new_list
}

} // verus!



// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpgzfe3lmr`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4
// Safe: False