
use vstd::prelude::*;

fn main() {}

verus! {
    fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
        requires
            list@.len() > 0,
            0 < n < list@.len(),
        ensures
            reversed_list@ == list@.subrange(0, n as int).reverse().add(
                list@.subrange(n as int, list.len() as int),
            ),
    {
        let mut reversed_list = Vec::new();
        let mut index = 0;
        while index < n
            invariant
                list@.len() > 0,
                0 < n < list@.len(),
                0 <= index <= n,
                reversed_list@ == list@.subrange(0, index as int).reverse(),
                reversed_list.len() == index,
                list.len() == list@.len(),
        {
            reversed_list.push(list[n - 1 - index]);
            index += 1;
            proof {
                // Assertion to ensure state consistency after each iteration
                assert(reversed_list@ == list@.subrange(0, index as int).reverse());
                assert(reversed_list.len() == index);
            }
        }
        index = n;
        while index < list.len()
            invariant
                list@.len() > 0,
                n <= index <= list@.len(),
                reversed_list@ == list@.subrange(0, n as int).reverse().add(list@.subrange(n as int, index as int)),
                reversed_list.len() == index,
                list.len() == list@.len(),
        {
            reversed_list.push(list[index]);
            index += 1;
            proof {
                // Assertion to ensure state consistency after each iteration
                assert(reversed_list@ == list@.subrange(0, n as int).reverse().add(list@.subrange(n as int, index as int)));
                assert(reversed_list.len() == index);
            }
        }
        reversed_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpuwym34rm`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True