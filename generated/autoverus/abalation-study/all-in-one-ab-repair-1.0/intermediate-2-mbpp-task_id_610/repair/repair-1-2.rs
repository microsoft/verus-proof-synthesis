
use vstd::prelude::*;
fn main() {}

verus! {

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 < k <= list@.len(), // Corrected to include k == len condition
    ensures
        new_list@ == list@.subrange(0, k - 1 as int).add(
            list@.subrange(k as int, list.len() as int),
        ),
{
    let mut new_list = Vec::new();
    let mut index = 0;
    
    while index < k - 1
        invariant
            forall|i: int| 0 <= i < index ==> new_list[i] == list[i],
            index <= k - 1,
            new_list.len() == index,
            new_list@.len() == index as int,
            list.len() == list@.len(),
            0 < k <= list@.len(),
    {
        new_list.push(list[index]);
        index += 1;
    }

    let mut index = k;
    
    while index < list.len()
        invariant
            forall|i: int| 0 <= i < k - 1 ==> new_list[i] == list[i],
            forall|i: int| k <= i < index ==> new_list[i - 1] == list[i],
            index <= list.len(),
            new_list.len() == index - 1,
            new_list@.len() == index as int - 1,
            list.len() == list@.len(),
            0 < k <= list@.len(),
    {
        new_list.push(list[index]);
        index += 1;
    }
    
    new_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpn8w4q2v8`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: False