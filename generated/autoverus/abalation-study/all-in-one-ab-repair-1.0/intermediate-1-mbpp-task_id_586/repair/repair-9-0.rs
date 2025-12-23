
use vstd::prelude::*;
fn main() {}

verus! {
    fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
        requires
            0 < list@.len(),
            0 < n < list@.len(),
        ensures
            new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
    {
        let mut new_list = Vec::new();
        let len = list.len(); // Store length for reusability
        let mut index = n;
        
        while index < len
            invariant
                0 < n < len,
                n <= index <= len,
                new_list@ == list@.subrange(n as int, (index as int)),
                len == old(list).len(),
        {
            new_list.push(list[index]);
            index += 1;
        }

        index = 0; // Reset index for the second loop

        while index < n
            invariant
                0 < n < len,
                0 <= index <= n,
                new_list@ == list@.subrange(n as int, len as int).add(list@.subrange(0, index as int)),
                len == old(list).len(),
        {
            new_list.push(list[index]);
            index += 1;
        }

        proof {
            let list_seq = list@;
            let final_new_list = new_list@;
            assert(final_new_list == list_seq.subrange(n as int, list_seq.len() as int).add(list_seq.subrange(0, n as int)));
        }

        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpwqni0fum`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False