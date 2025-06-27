
use vstd::prelude::*;
fn main() {}

verus! {

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 <= k < list@.len(), // Fixed: using 0 <= k to include 0 index
    ensures
        new_list@ == list@.subrange(0, k as int).add(list@.subrange(k as int + 1, list.len())),
{
    let mut new_list = Vec::new();
    let mut index = 0;

    // Loop to copy elements before k
    while index < k
        invariant
            list.len() > 0,
            0 <= k < list@.len(),
            index <= k,
            new_list.len() == index,
            forall|i: int| 0 <= i < index ==> new_list.view()[i] == list.view()[i],
    {
        new_list.push(list[index]);
        index += 1;
    }

    // Continue copying from k + 1 to the end
    let mut idx = k + 1; // Fixed redeclaration of the index variable.
    while idx < list.len()
        invariant
            list.len() > 0,
            0 <= k < list@.len(),
            k <= idx <= list.len(),
            new_list.len() == idx - 1,
            forall|i: int| 0 <= i < k ==> new_list.view()[i] == list.view()[i],
            forall|i: int| k + 1 <= i < idx ==> new_list.view()[i - 1] == list.view()[i],
    {
        new_list.push(list[idx]);
        idx += 1;
    }

    new_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpx6y2airf`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False