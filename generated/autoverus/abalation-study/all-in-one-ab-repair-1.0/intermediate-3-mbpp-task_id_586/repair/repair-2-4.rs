
use vstd::prelude::*;
fn main() {}

verus! {

    fn split_and_append(list: &Vec<i32>, n: usize) -> Vec<i32>
        requires
            list@.len() > 0,
            0 < n < list@.len(),
        ensures
            result@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
    {
        let mut new_list = Vec::new();
        let mut index = n;
        while index < list.len()
            invariant
                0 <= n < list@.len(),
                n <= index <= list.len(),
                new_list@ == list@.subrange(n as int, index as int),
                list@.len() == list.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }
        let mut index = 0;
        while index < n
            invariant
                0 <= n < list@.len(),
                0 <= index <= n,
                new_list@ == list@.subrange(n as int, list@.len() as int).add(
                    list@.subrange(0, index as int),
                ),
                list@.len() == list.len(),
        {
            new_list.push(list[index]);
            index += 1;
        }
        new_list
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpiu14qxzb`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False