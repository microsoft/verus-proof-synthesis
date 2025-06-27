
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
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
        // First loop: copy elements before k-1
        while index < (k - 1)
            invariant
                forall|i: int| 0 <= i < index ==> new_list[i as usize] == list[i as usize],
                index < k - 1, // Fixed the boundary invariant
                new_list.len() == index,
                new_list@.len() == index as int,
                list.len() > 0,
                0 < k < list@.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }
        
        // Second loop: copy elements after k
        let mut index = k;
        while index < list.len()
            invariant
                forall|i: int| 0 <= i < k - 1 ==> new_list[i as usize] == list[i as usize],
                forall|i: int| k <= i < index ==> new_list[(i - (k - 1)) as usize] == list[i as usize],
                index <= list.len(),
                new_list.len() == index - k + 1, // Updated the length invariant
                new_list@.len() == (index - k + 1) as int, // Updated the length invariant
                list.len() > 0,
                0 < k < list@.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }
        new_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpu_gu2gh0`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: True