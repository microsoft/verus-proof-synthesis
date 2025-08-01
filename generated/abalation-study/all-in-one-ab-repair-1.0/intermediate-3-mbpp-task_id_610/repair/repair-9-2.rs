
use vstd::prelude::*;
fn main() {}

verus! {
    fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
        requires
            list.len() > 0,
            0 <= k < list@.len(),
        ensures
            new_list@ == list@.subrange(0, k as int).add(
                list@.subrange(k as int + 1 as int, list.len() as int),
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

        // Continue copying from k+1 to the end
        let mut index = k + 1; // Re-declaring the mutable variable index
        while index < list.len()
            invariant
                list.len() > 0,
                0 <= k < list@.len(),
                k + 1 <= index <= list.len(),
                k + index - k - 1 == new_list.len(), // Here we update the length invariant
                forall|i: int| 0 <= i < k ==> new_list.view()[i] == list.view()[i],
                forall|i: int| k + 1 <= i < index ==> new_list.view()[i - 1] == list.view()[i],
        {
            new_list.push(list[index]);
            index += 1;
        }

        new_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpz775v5jb`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: False