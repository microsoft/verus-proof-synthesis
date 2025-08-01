
use vstd::prelude::*;
fn main() {}
verus! {

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 < k < list@.len(),
    ensures
        new_list@ == list@.subrange(0, k as int - 1).add(list@.subrange(k as int, list.len() as int)),
{
    let mut new_list = Vec::new();
    let mut index = 0;
    while index < (k - 1)
        invariant
            forall|i: int| 0 <= i < index ==> new_list[i as usize] == list[i as usize],
            index < k,
            new_list.len() == index,
    {
        new_list.push(list[index]);
        index += 1;
    }
    
    index = k;
    while index < list.len()
        invariant
            forall|i: int| 0 <= i < k - 1 ==> new_list[i as usize] == list[i as usize],
            forall|i: int| k <= i < index ==> new_list[i as usize - 1] == list[i as usize],
            index <= list.len(),
            new_list.len() == index - 1,
    {
        new_list.push(list[index]);
        index += 1;
    }
    new_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmprgo37y_b`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: False