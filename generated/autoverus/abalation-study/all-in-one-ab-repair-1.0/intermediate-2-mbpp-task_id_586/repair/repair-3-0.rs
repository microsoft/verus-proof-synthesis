
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
                forall |k: int| 0 <= k < new_list.len() ==> new_list[k] == list[(n + k) as usize],
        {
            proof {
                assert(forall |k: int| 0 <= k < new_list.len() ==> new_list[k] == list[(n + k) as usize]);
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
                new_list@ == list@.subrange(n as int, list@.len() as int).add(
                    list@.subrange(0, index as int),
                ),
                forall |k: int| 0 <= k < new_list.len() ==> (if k < (list.len() as int - n as int) {
                    new_list[k] == list[(n + k) as usize]
                } else {
                    new_list[k] == list[(k - (list.len() as int - n as int)) as usize]
                }),
        {
            proof {
                assert(forall |k: int| 0 <= k < new_list.len() ==> (if k < (list.len() as int - n as int) {
                    new_list[k] == list[(n + k) as usize]
                } else {
                    new_list[k] == list[(k - (list.len() as int - n as int)) as usize]
                }));
            }
            new_list.push(list[index]);
            index += 1;
        }
        new_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpse1hjjqf`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: True