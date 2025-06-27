
use vstd::prelude::*;
fn main() {}

verus! {
    fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
        requires
            list.len() > 0,
            0 <= k < list@.len() as usize, // Corrected range for k.
        ensures
            new_list@ == list@.subrange(0, k as int).add(
                list@.subrange((k + 1) as int, list.len() as int),
            ),
    {
        let mut new_list = Vec::new();
        let mut index = 0;

        // Loop to copy elements before k.
        while index < k
            invariant
                list.len() > 0,
                0 <= k < list@.len() as usize,
                index <= k,
                new_list.len() == index,
                forall|i: int| 0 <= i < index ==> new_list.view()[i] == list.view()[i],
        {
            new_list.push(list[index]);
            index += 1;
        }

        // Continue copying from k + 1 to the end.
        let mut index2 = k + 1; // Changed variable name to avoid redeclaration.
        while index2 < list.len()
            invariant
                list.len() > 0,
                0 <= k < list@.len() as usize,
                k + 1 <= index2 <= list.len(),
                k + (index2 - k - 1) == new_list.len(), // Here we update the length invariant.
                forall|i: int| 0 <= i < k ==> new_list.view()[i] == list.view()[i],
                forall|i: int| k + 1 <= i < index2 ==> new_list.view()[i - 1] == list.view()[i],
        {
            new_list.push(list[index2]);
            index2 += 1;
        }

        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmptjqez6rn`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: False