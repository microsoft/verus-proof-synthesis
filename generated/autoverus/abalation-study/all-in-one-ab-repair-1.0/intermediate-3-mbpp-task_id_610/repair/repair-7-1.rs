
use vstd::prelude::*;
fn main() {}

verus! {

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 <= k < list@.len(),
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
            0 <= k < list@.len(),
            index <= k,
            new_list.len() == index,
            forall|i: int| 0 <= i < index ==> new_list.view()[i] == list.view()[i],
    {
        new_list.push(list[index]);
        index += 1;
    }

    // Update index to skip k and continue copying from k+1 to the end
    let mut new_index = k + 1;
    while new_index < list.len()
        invariant
            list.len() > 0,
            0 <= k < list@.len(),
            k + 1 <= new_index <= list.len(),
            index + (new_index - k - 1) == new_list.len(), // here we update the length invariant
            forall|i: int| 0 <= i < index ==> new_list.view()[i] == list.view()[i],
            forall|i: int| k + 1 <= i < new_index ==> new_list.view()[i - 1] == list.view()[i],
    {
        new_list.push(list[new_index]);
        new_index += 1;
    }

    new_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpilo9cv_v`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: False