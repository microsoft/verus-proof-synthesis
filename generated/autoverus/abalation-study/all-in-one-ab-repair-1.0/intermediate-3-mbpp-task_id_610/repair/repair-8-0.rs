
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

        // Loop to copy elements before k-1
        while index < (k - 1)
            invariant
                list.len() > 0,
                0 < k < list@.len(),
                index <= k - 1,
                new_list.len() == index,
                forall|i: int| 0 <= i < index ==> new_list@[i as nat] == list@[i as nat],
        {
            new_list.push(list[index]);
            index += 1;
        }

        // Update index to k and continue copying from k to the end
        let mut index = k; // Re-declaring the mutable variable index
        while index < list.len()
            invariant
                list.len() > 0,
                0 < k < list@.len(),
                k <= index <= list.len(),
                (k - 1) + (index - k) == new_list.len(),
                forall|i: int| 0 <= i < k - 1 ==> new_list@[i as nat] == list@[i as nat],
                forall|i: int| k <= i < index ==> new_list@[(i - 1) as nat] == list@[i as nat],
        {
            new_list.push(list[index]);
            index += 1;
        }

        new_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmplw9ehmng`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: False