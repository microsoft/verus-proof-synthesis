
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
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
        {
            new_list.push(list[index]);

            proof {
                assert(list@.subrange(n as int, index as int + 1) == new_list@.add(seq![list[index]]));
            }

            index += 1;
        }

        let mut index = 0;

        while index < n
            invariant
                0 < n < list@.len(),
                0 <= index <= n,
                list@.len() > 0,
                new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, index as int)),
        {
            new_list.push(list[index]);

            proof {
                assert(list@.subrange(0, index as int + 1) == seq![list[index]].add(list@.subrange(1, index as int)));
                assert(new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, index as int + 1)));
            }

            index += 1;
        }

        new_list // returns new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpfe7mt157`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True