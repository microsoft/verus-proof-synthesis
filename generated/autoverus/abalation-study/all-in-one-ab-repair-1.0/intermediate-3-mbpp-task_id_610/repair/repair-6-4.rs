
use vstd::prelude::*;
fn main() {}

verus! {

spec fn seq_remove_kth(a: Seq<i32>, k: int) -> Seq<i32> {
    a.subrange(0, k) + a.subrange(k + 1, a.len())
}

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 <= k < list@.len(),
    ensures
        new_list@ == seq_remove_kth(list@, k as int),
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
            forall|i: int| 0 <= i < index ==> new_list[i] == list[i],
    {
        new_list.push(list[index]);
        index += 1;
    }

    // Skip element at position k and continue copying from k+1 to the end
    let mut index = k + 1;
    while index < list.len()
        invariant
            list.len() > 0,
            0 <= k < list@.len(),
            k < index <= list.len(),
            (k) + (index - (k + 1)) == new_list.len(),
            forall|i: int| 0 <= i < k ==> new_list[i] == list[i],
            forall|i: int| k + 1 <= i < index ==> new_list[i - 1] == list[i],
    {
        new_list.push(list[index]);
        index += 1;
    }

    new_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp42_mv0qh`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False