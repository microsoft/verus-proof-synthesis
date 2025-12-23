
use vstd::prelude::*;
fn main() {}
verus! {

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 < k < list@.len(),
    ensures
        new_list@ == list@.subrange(0, k as int).add(
            list@.subrange(k as int + 1, list.len() as int),
        ),
{
    let mut new_list = Vec::new();
    let mut index = 0;
    
    while index < k
        invariant
            forall|i: int| 0 <= i < index ==> new_list@.index(i) == list@.index(i as usize),
            new_list.len() == index,
            index <= k,
            list.len() > 0,
            0 < k < list@.len(),
    {
        new_list.push(list[index]);
        index += 1;
    }

    index += 1;

    while index < list.len()
        invariant
            forall|i: int| 0 <= i < k ==> new_list@.index(i) == list@.index(i),
            forall|i: int| k <= i < index - 1 ==> new_list@.index(i) == list@.index(i + 1),
            new_list.len() == index - 1,
            index - 1 >= k,
            index <= list.len(),
            list.len() > 0,
            0 < k < list@.len(),
    {
        new_list.push(list[index]);
        index += 1;
    }
    
    new_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpdat63u4f`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False