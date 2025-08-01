
use vstd::prelude::*;
fn main() {}

verus! {
    fn split_and_append(list: &Vec<i32>, n: usize) -> Vec<i32>
        requires
            list@.len() > 0,
            0 < n && n < list@.len(),
        ensures
            list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)) == new_list@,
    {
        let mut new_list = Vec::new();
        let mut index = n;

        while index < list.len()
            invariant
                0 < n && n < list@.len(), // n is between 0 and the length of the list, exclusive
                list@.len() > 0, // the length of the list should be greater than 0
                n <= index && index <= list.len(), // index is between n and list length
                new_list@ == list@.subrange(n as int, index as int), // Partial new_list contains elements from n to current index
        {
            new_list.push(list[index]);
            index += 1;
        }

        let mut index = 0;

        while index < n
            invariant
                0 < n && n < list@.len(), // n is between 0 and the length of the list, exclusive
                0 <= index && index <= n, // index is between 0 and n, inclusive
                list@.len() > 0, // the length of the list should be greater than 0
                new_list@ == list@.subrange(n as int, list@.len() as int).add(
                    list@.subrange(0, index as int),
                ), // new_list contains elements from n to end, plus current range from 0 to index
        {
            new_list.push(list[index]);
            index += 1;
        }

        proof {
            assert(new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)));
        }

        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp33wsawe9`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False