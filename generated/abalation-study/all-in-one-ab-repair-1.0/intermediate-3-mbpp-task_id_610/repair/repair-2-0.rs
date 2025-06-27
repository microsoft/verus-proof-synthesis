
use vstd::prelude::*;
fn main() {}

verus! {
    fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
        requires
            list.len() > 0,
            0 < k < list@.len(),
        ensures
            new_list@ == list@.subrange(0, k as int - 1).add(
                list@.subrange(k as int, list.len() as int),
            ),
    {
        let mut new_list = Vec::new();
        let mut index = 0;
        while index < k
            invariant
                forall|i: int| 0 <= i < index ==> new_list.view()[i] == list.view()[i],
                index < k,
                new_list.len() == index,
                list.len() > 0,
                0 < k < list@.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }

        let mut index = k;
        while index < list.len()
            invariant
                forall|i: int| 0 <= i < k => new_list.view()[i] == list.view()[i],
                forall|i: int| k <= i < index ==> new_list.view()[i - 1] == list.view()[i],
                index <= list.len(),
                new_list.len() == index - 1,
                list.len() > 0,
                0 < k < list@.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }
        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp7mbxrw71`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False