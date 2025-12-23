
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
        requires
            list.len() > 0,
            0 <= k < list@.len() as usize,
        ensures
            new_list@ == list@.subrange(0, k as int).add(
                list@.subrange((k + 1) as int, list.len() as int),
            ),
    {
        let mut new_list = Vec::new();
        let mut index = 0;
        // First loop: copy elements before k
        while index < k
            invariant
                forall|i: int| 0 <= i < index as int ==> new_list[i as usize] == list[i as usize],
                index <= k,
                new_list.len() == index,
                new_list@.len() == index as int,
                list.len() > 0,
                0 <= k < list@.len() as usize,
        {
            new_list.push(list[index]);
            index += 1;
        }

        // Second loop: copy elements after k
        while index + 1 < list.len()
            invariant
                forall|i: int| 0 <= i < k as int ==> new_list[i as usize] == list[i as usize],
                forall|i: int| k as int < i < (index + 1) as int ==> new_list[(i - 1) as usize] == list[i as usize],
                index + 1 <= list.len(),
                new_list.len() == index,
                new_list@.len() == index as int,
                list.len() > 0,
                0 <= k < list@.len() as usize,
        {
            new_list.push(list[index + 1]);
            index += 1;
        }

        new_list // Return the new list without the kth element
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp8lsxqnkf`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False