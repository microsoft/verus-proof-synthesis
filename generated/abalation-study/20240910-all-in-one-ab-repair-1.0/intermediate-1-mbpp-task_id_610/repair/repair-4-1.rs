
use vstd::prelude::*;
fn main() {}

verus! {
    fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
        requires
            list.len() > 0,
            0 <= k < list@.len() as usize, // Modified the condition to be inclusive of 0 and handle boundaries correctly
        ensures
            new_list@ == list@.subrange(0, k as int).add(
                list@.subrange(k as int + 1, list.len() as int),
            ),
    {
        let mut new_list = Vec::new();
        let mut index = 0;

        // Loop to copy elements from 0 to k-1 (inclusive)
        while index < k
            invariant
                index <= k,
                forall|i: int| 0 <= i < index ==> new_list[i] == list[i],
                new_list.len() == index,
                list.len() > 0,
                0 <= k < list@.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }

        // Loop to copy elements from k+1 to the end
        index = k + 1;
        while index < list.len()
            invariant
                index > k,
                index <= list.len(),
                forall|i: int| 0 <= i < k ==> new_list[i] == list[i],
                forall|i: int| k < i < index ==> new_list[i - 1] == list[i],
                new_list.len() == index - 1,
                list.len() > 0,
                0 <= k < list@.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }

        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmppvxduidi`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: False