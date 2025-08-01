
use vstd::prelude::*;
fn main() {}

verus! {

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 < k < list@.len(),
    ensures
        new_list@ == list@.subrange(0, k - 1 as int).add(
            list@.subrange(k as int, list.len() as int),
        ),
{
    let mut new_list = Vec::new();
    let mut index = 0;

    // Loop to copy elements before k-1
    while index < (k - 1)
        invariant
            list.len() > 0,
            0 < k < list@.len(),
            index <= k - 1,
            new_list.len() == index,
            forall|i:int| 0 <= i < index ==> new_list.view()[i] == list.view()[i],
    {
        new_list.push(list[index]);
        index += 1;
    }

    // Update index to k and continue copying from k to the end
    index = k;  // Changed the definition
    while index < list.len()
        invariant
            list.len() > 0,
            0 < k < list@.len(),
            k <= index <= list.len(),
            new_list.len() == (k - 1) + (index - k + 1), // Updated invariant for better clarity
            forall|i:int| 0 <= i < k - 1 ==> new_list.view()[i] == list.view()[i],
            forall|i:int| k <= i < index ==> new_list.view()[i - 1] == list.view()[i],
    {
        new_list.push(list[index]);
        index += 1;
    }

    new_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp_971ybcf`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3
// Safe: False