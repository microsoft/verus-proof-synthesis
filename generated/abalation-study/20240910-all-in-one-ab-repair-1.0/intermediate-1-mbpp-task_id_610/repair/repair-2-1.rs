
use vstd::prelude::*;
fn main() {}

verus! {

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 <= k < list@.len(),
    ensures
        new_list@ == list@.subrange(0, k).add(list@.subrange(k + 1, list.len() as int)),
{
    let mut new_list = Vec::new();
    let mut index = 0;
    
    while index < k
        invariant
            forall|i: int| 0 <= i < index ==> new_list@.index(i) == list@.index(i),
            new_list.len() == index,
            new_list@.len() == index,
            list.len() == list.len(),
            0 <= k < list@.len(),
            index <= k,
            list.len() > 0,
    {
        new_list.push(list[index]);
        index += 1;
    }
    
    index = k + 1;
    
    while index < list.len()
        invariant
            forall|i: int| 0 <= i < k ==> new_list@.index(i) == list@.index(i),
            forall|i: int| k + 1 <= i < index ==> new_list@.index(i - 1) == list@.index(i),
            new_list.len() == index - 1,
            new_list@.len() == index - 1,
            list.len() == list.len(),
            0 <= k < list@.len(),
            index > k,
            index <= list.len(),
            list.len() > 0,
    {
        new_list.push(list[index]);
        index += 1;
    }

    new_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpxxbd2x4h`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False