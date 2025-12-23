
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
        {
            new_list.push(list[index]);
            proof {
                // Loop Invariant maintenance steps
                let subrange_len = (index - n) as int;
            }
            index += 1;
        }

        let mut index = 0;
        while index < n
            invariant
                0 < n < list@.len(),
                0 <= index <= n,
                list@.len() > 0,
        {
            new_list.push(list[index]);
            proof {
                // Loop Invariant maintenance steps
                let current_len = new_list@.len() as int - (list@.len() as int - n as int);
            }
            index += 1;
        }

        proof {
            let list_seq = list@;
            let final_new_list = new_list@;
        }

        new_list
    }
}


// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1