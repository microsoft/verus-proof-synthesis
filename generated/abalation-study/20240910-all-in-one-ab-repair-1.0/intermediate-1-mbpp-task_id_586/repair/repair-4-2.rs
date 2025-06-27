
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
                new_list@ == list@.subrange(n as int, index as int),
                list.len() == old(list).len(), // Loop invariant specifying the length of the array
        {
            new_list.push(list[index]);
            index += 1;
        }
        
        let mut index = 0;
        while index < n
            invariant
                0 < n < list@.len(),
                0 <= index <= n,
                list@.len() > 0,
                new_list@ == list@.subrange(n as int, list@.len() as int).add(
                    list@.subrange(0, index as int),
                ),
                list.len() == old(list).len(), // Loop invariant specifying the length of the array
        {
            new_list.push(list[index]);
            index += 1;
        }
        
        proof {
            // This proof block can help in maintaining the correctness of the final result.
            let new_sub1 = list@.subrange(n as int, list@.len() as int);
            let new_sub2 = list@.subrange(0, n as int);
            assert(new_list@ == new_sub1.add(new_sub2));
        }
        
        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp8y4j0kfo`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True