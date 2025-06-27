
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::proof]
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
            proof {
                assert(0 <= n < list.len());
                assert(forall|k: int| (n as int) <= k < (index as int) ==>
                        new_list[(k - (n as int)) as usize] == list[k as usize]);
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
        {
            proof {
                assert(0 <= n < list.len());
                assert(forall|k: int| (list.len() as int - n as int + 0) <= k < (list.len() as int - n as int + index as int) ==>
                        new_list[k as usize] == list[(index as int - (list.len() as int - n)) as usize]);
            }
            new_list.push(list[index]);
            index += 1;
        }

        new_list // returns new_list
    }
}

// Score: (0, 4)
// Safe: True