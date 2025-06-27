
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
    while index < k
        invariant
            forall|i: int| 0 <= i < index ==> new_list[i] == list[i],
            index <= k,
            new_list.len() == index,
            new_list@.len() == index,
            list.len() > 0,
            0 < k < list@.len(),
    {
        new_list.push(list[index]);
        index += 1;
    }

    let mut index_2 = k + 1;  // Using a different index name for the second loop
    while index_2 < list.len()
        invariant
            forall|i: int| 0 <= i < k ==> new_list[i] == list[i],
            forall|i: int| k < i < index_2 ==> new_list[i - 1] == list[i],
            index_2 <= list.len(),
            new_list.len() == index_2 - 1,
            new_list@.len() == index_2 - 1,
            list.len() > 0,
            0 < k < list@.len(),
    {
        new_list.push(list[index_2]);
        index_2 += 1;
    }
    new_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpt6ucprzl`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2
// Safe: False