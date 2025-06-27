
use vstd::prelude::*;
fn main() {}

verus! {
    fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
        requires
            list.len() > 0,
            0 <= k < list@.len(),
        ensures
            new_list@ == list@.subrange(0, k as int).add(
                list@.subrange(k as int + 1, list.len() as int)
            ),
    {
        let mut new_list = Vec::new();
        let mut index = 0;
        while index < k
            invariant
                forall|i: int| 0 <= i < index ==> new_list[i] == list[i],
                index <= k, 
                new_list.len() == index,
                new_list@.len() == index,
        {
            new_list.push(list[index]);
            index += 1;
        }
        let mut index = k + 1;
        while index < list.len()
            invariant
                forall|i: int| 0 <= i < k ==> new_list[i] == list[i],
                forall|i: int| k + 1 <= i < index ==> new_list[i - 1] == list[i],
                index <= list.len(),
                new_list.len() == index - 1,
                new_list@.len() == index - 1,
        {
            new_list.push(list[index]);
            index += 1;
        }
        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpyx4xrm14`)
// 

// Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 3
// Safe: False