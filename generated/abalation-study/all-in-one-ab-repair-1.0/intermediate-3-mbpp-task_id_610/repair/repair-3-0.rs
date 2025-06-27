
use vstd::prelude::*;
fn main() {}

verus! {

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 <= k < list@.len(),
    ensures
        new_list@ == list@.subrange(0, k as int).add(
            list@.subrange(k as int + 1, list.len() as int),
        ),
{
    let mut new_list = Vec::new();
    let mut index = 0;

    // Loop to copy elements before k
    while index < k
        invariant
            list.len() > 0,
            0 <= k < list@.len(),
            0 <= index <= k,
            new_list.len() == index,
            forall|i: int| 0 <= i < index ==> new_list.view()[i] == list.view()[i],
    {
        new_list.push(list[index]);
        index += 1;
    }

    index += 1;  // Skip the k-th element

    // Continue copying from k+1 to the end
    while index < list.len()
        invariant
            list.len() > 0,
            0 <= k < list@.len(),
            k + 1 <= index <= list.len(),
            new_list.len() == index - 1,
            forall|i: int| 0 <= i < k ==> new_list.view()[i] == list.view()[i],
            forall|i: int| k + 1 <= i < index ==> new_list.view()[i - 1] == list.view()[i],
    {
        new_list.push(list[index]);
        index += 1;
    }

    new_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpmrun04kd`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: False