
use vstd::prelude::*;
fn main() {}

verus! {

    spec fn split_and_append_spec(list: Seq<i32>, n: int) -> Seq<i32> {
        list.subrange(n, list.len()).add(list.subrange(0, n))
    }

    fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
        requires
            list@.len() > 0,
            0 < n < list@.len(),
        ensures
            new_list@ == split_and_append_spec(list@, n as int),
    {
        let mut new_list = Vec::new();
        let len = list.len();
        let mut index = n;

        while index < len
            invariant
                0 < n < list@.len(),
                list@.len() > 0,
                n <= index <= len,
                new_list@ == list@.subrange(n as int, index as int),
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
                new_list@ == list@.subrange(n as int, len as int).add(list@.subrange(0, index as int)),
        {
            new_list.push(list[index]);
            index += 1;
        }

        // Check final postcondition in proof block
        proof {
            assert(new_list@ == split_and_append_spec(list@, n as int));
        }
        
        new_list
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpom58phjw`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False