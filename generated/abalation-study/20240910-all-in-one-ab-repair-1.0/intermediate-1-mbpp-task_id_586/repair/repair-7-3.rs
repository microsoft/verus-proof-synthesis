
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
        let mut index = n;
        while index < list.len()
            invariant
                0 < n < list@.len(),
                list@.len() > 0,
                n <= index <= list.len(),
                new_list@ == list@.subrange(n as int, (index as int)),
                list.len() == old(list).len(),
        {
            proof {
                assert(n <= index < list.len()); // Proof step to show that index is within bounds
            }
            new_list.push(list[index]);
            index += 1;
        }
        let mut index = 0;
        while index < n
            invariant
                0 < n < list@.len(),
                0 <= index <= n,
                list@.len() > 0,
                new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, index as int)),
                list.len() == old(list).len(),
        {
            proof {
                assert(0 <= index < n); // Proof step to ensure index is within bounds for the second loop
            }
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpplikrov1`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True