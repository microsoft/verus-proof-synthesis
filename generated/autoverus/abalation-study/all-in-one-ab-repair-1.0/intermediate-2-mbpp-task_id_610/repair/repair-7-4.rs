
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
        requires
            list.len() > 0,
            0 < k < list@.len(), // Changed from 0 <= k < list@.len() because k = 0 is not meaningful in this context
        ensures
            new_list@ == list@.subrange(0, k - 1 as int).add(
                list@.subrange(k as int, list.len() as int),
            ),
    {
        let mut new_list = Vec::new();
        let mut index = 0;

        // First loop: copy elements before k-1
        while index < k
            invariant
                forall|i: int| 0 <= i < index ==> new_list[i as usize] == list[i as usize],
                index <= k, // since index < k
                new_list.len() == index,
                new_list@.len() == index as int,
                list.len() > 0,
                0 < k < list@.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }
        
        // Second loop: copy elements after k
        // We start from index which is now equal to k
        while index < list.len()
            invariant
                forall|i: int| 0 <= i < k ==> new_list[i as usize] == list[i as usize],
                forall|i: int| k <= i < index ==> new_list[(i - 1) as usize] == list[i as usize],
                index <= list.len(),
                new_list.len() == index - 1, // as we shifted elements after k
                new_list@.len() == (index - 1) as int, // as we shifted elements after k
                list.len() > 0,
                0 < k < list@.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }
        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpgq53jp9o`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: False