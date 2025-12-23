
use vstd::prelude::*;
fn main() {}

verus! {
    fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
        requires
            list@.len() > 0,
            0 < n < list@.len(),
        ensures
            new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
    {
        let mut new_list = Vec::new();
        let list_len = list.len(); // Save the list length to avoid repetitive calls
        let mut index = n;

        while index < list_len
            invariant
                0 < n < list_len,
                list@.len() > 0,
                n <= index <= list_len,
                new_list@ == list@.subrange(n as int, index as int),
        {
            new_list.push(list[index]);
            index += 1;
        }

        let mut index = 0;

        while index < n
            invariant
                0 < n < list_len,
                0 <= index <= n,
                list@.len() > 0,
                new_list@ == list@.subrange(n as int, list_len as int).add(list@.subrange(0, index as int)),
        {
            new_list.push(list[index]);
            index += 1;
        }

        new_list // returns new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpo6trrgwc`)
// 

// Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 6
// Safe: False