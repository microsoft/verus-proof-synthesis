
use vstd::prelude::*;
fn main() {}

verus! {
    
#[verifier::loop_isolation(false)]
fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 < k < list@.len(),
    ensures
        new_list@ == list@.subrange(0, k as int).add(
            list@.subrange((k + 1) as int, list.len() as int),
        ),
{
    let mut new_list = Vec::new();
    let mut index = 0;
    
    // First loop: account for elements before `k`
    while index < k
        invariant
            forall|i: int| 0 <= i < index ==> new_list@index(i) == list@index(i),
            index <= k,
            new_list.len() == index,
            list.len() > 0,
            0 < k < list@.len(),
            list@.len() == list.len(),
    {
        new_list.push(list[index]);
        index += 1;
    }
    
    // Second loop: account for elements after `k`
    let mut index = k + 1;
    while index < list.len()
        invariant
            forall|i: int| 0 <= i < k ==> new_list@index(i) == list@index(i),
            forall|i: int| k < i <= index ==> new_list@index(i - 1) == list@index(i),
            index <= list.len(),
            new_list.len() == index - 1,
            list.len() > 0,
            0 < k < list@.len(),
            list@.len() == list.len(),
    {
        new_list.push(list[index]);
        index += 1;
    }
    
    new_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp5d4b3bim`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False