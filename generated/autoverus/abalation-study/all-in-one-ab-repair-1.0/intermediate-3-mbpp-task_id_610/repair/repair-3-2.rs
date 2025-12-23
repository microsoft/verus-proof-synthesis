
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

    // Loop to copy elements before k
    while index < k
        invariant
            list.len() > 0,
            0 < k < list@.len(),
            index <= k,
            new_list.len() == index,
            forall|i: int| 0 <= i < index ==> new_list.view()[i as usize] == list.view()[i as usize],
    {
        new_list.push(list[index]);
        index += 1;
    }

    // Skipping the kth element
    index += 1;

    // Continue copying from k+1 to the end
    while index < list.len()
        invariant
            list.len() > 0,
            0 < k < list@.len(),
            k < index <= list.len(),
            new_list.len() == index - 1,
            forall|i: int| 0 <= i < k ==> new_list.view()[i as usize] == list.view()[i as usize],
            forall|i: int| k < i < index ==> new_list.view()[(i - 1) as usize] == list.view()[i as usize],
    {
        new_list.push(list[index]);
        index += 1;
    }

    new_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp7c2bcb9n`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: False