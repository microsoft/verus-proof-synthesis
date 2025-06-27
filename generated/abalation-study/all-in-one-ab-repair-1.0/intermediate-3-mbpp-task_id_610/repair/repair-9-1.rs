
use vstd::prelude::*;
fn main() {}

verus! {
    fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
        requires
            list.len() > 0,
            0 <= k < list@.len(), // Corrected from `0 < k < list@.len()` to `0 <= k < list@.len()`
        ensures
            new_list@ == list@.subrange(0, k as int).add(
                list@.subrange((k + 1) as int, list@.len()),
            ),
    {
        let mut new_list = Vec::new();
        let mut index = 0;

        // Loop to copy elements before k
        while index < k
            invariant
                list.len() > 0,
                0 <= k < list@.len(), // Updated invariant
                index <= k,
                new_list.len() == index,
                forall|i: int| 0 <= i < index ==> new_list.view()[i] == list.view()[i],
        {
            new_list.push(list[index]);
            index += 1;
        }

        // Increment index to k+1 and continue copying from k+1 to the end
        let mut index = k + 1; 
        while index < list.len()
            invariant
                list.len() > 0,
                0 <= k < list@.len(), // Updated invariant
                k + 1 <= index <= list.len(),
                k + (index - k - 1) == new_list.len(), // Here we update the length invariant
                forall|i: int| 0 <= i < k ==> new_list.view()[i] == list.view()[i],
                forall|i: int| k + 1 <= i < index ==> new_list.view()[(i - 1) as usize] == list.view()[i],
        {
            new_list.push(list[index]);
            index += 1;
        }

        new_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp17tzhtsm`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False