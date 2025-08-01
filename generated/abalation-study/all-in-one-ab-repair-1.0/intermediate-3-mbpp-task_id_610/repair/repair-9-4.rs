
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

        // Loop to copy elements before k-1 (inclusive)
        while index < k - 1
            invariant
                list.len() > 0,
                0 < k < list@.len(),
                index <= k - 1,
                new_list.len() == index,
                forall|i: int| 0 <= i < index ==> new_list.view()[i] == list.view()[i],
        {
            new_list.push(list[index]);
            index += 1;
        }

        // Skip the k-th element by updating index to k
        index = k; // Re-declaring the mutable variable index
        while index < list.len()
            invariant
                list.len() > 0,
                0 < k < list@.len(),
                k <= index <= list.len(),
                new_list.len() == (k - 1) + (index - k),
                forall|i: int| 0 <= i < k - 1 ==> new_list.view()[i] == list.view()[i],
                forall|i: int| k <= i < index ==> new_list.view()[i - 1] == list.view()[i],
        {
            new_list.push(list[index]);
            index += 1;
        }

        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpd5_s6ql3`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: False