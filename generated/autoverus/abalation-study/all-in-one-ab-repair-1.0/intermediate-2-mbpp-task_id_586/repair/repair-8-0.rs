
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

        // First loop to append elements from n to the end of the list
        while index < list.len()
            invariant
                0 < n < list@.len(),
                list@.len() > 0,
                n <= index <= list.len(),
                new_list@ == list@.subrange(n as int, index as int),
        {
            new_list.push(list[index]);
            proof {
                let current_len = new_list@.len();
                assert(new_list@ == list@.subrange(n as int, index as int));
                assert(new_list@ == list@.subrange(n as int, (n + current_len) as int));
            }
            index += 1;
        }

        index = 0;

        // Second loop to append elements from the start of the list to n
        while index < n
            invariant
                0 < n < list@.len(),
                0 <= index <= n,
                list@.len() > 0,
                new_list@ == list@.subrange(n as int, list@.len() as int).add(
                    list@.subrange(0, index as int),
                ),
        {
            new_list.push(list[index]);
            proof {
                let current_len = new_list@.len() - (list@.len() as int - n as int);
                assert(new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, current_len)));
            }
            index += 1;
        }

        proof {
            assert(new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)));
        }

        new_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpf4huvw8c`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: False