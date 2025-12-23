
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
        let list_len = list.len(); // Store the original length of the list
        // First loop: append the elements from index n to the end of the list
        let mut index = n;
        while index < list_len
            invariant
                0 < n < list@.len(),
                list@.len() > 0,
                n <= index <= list_len,
                new_list@ == list@.subrange(n as int, index as int),
                list_len == old(list).len(), // Loop invariant specifying the length of the array
        {
            new_list.push(list[index]);
            index += 1;
        }
        // Second loop: append the elements from start to index n-1
        let mut index = 0;
        while index < n
            invariant
                0 < n < list@.len(),
                0 <= index <= n,
                list@.len() > 0,
                new_list@ == list@.subrange(n as int, list@.len() as int).add(
                    list@.subrange(0, index as int),
                ),
                list_len == old(list).len(), // Loop invariant specifying the length of the array
        {
            new_list.push(list[index]);
            index += 1;
        }
        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmppl4j0op_`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False