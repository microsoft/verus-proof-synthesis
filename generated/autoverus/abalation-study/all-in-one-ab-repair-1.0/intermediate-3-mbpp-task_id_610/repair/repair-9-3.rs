
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
        while index < k
            invariant
                list.len() > 0,
                0 < k < list@.len(),
                index <= k,
                new_list.len() == index,
                forall|i: int| 0 <= i < index ==> new_list.view()[i] == list.view()[i],
        {
            new_list.push(list[index]);
            index += 1;
        }
        
        // Continue copying from k to the end
        while index < list.len()
            invariant
                list.len() > 0,
                0 < k < list@.len(),
                k <= index <= list.len(),
                (index - 1) == new_list.len(), // Adjusted invariant
                forall|i: int| 0 <= i < k ==> new_list.view()[i] == list.view()[i],
                forall|i: int| k <= i < index ==> new_list.view()[i - 1] == list.view()[i],
        {
            new_list.push(list[index]);
            index += 1;
        }

        new_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpwfo7tnlg`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3
// Safe: False