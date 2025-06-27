
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
        
        // Proof block for the initial state before entering the loop
        proof {
            assert(list@.len() > 0);
            assert(0 < n < list@.len());
        }

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
        }

        index = n;
        while index < list.len()
            invariant
                list@.len() > 0,
                n <= index <= list.len(),
                reversed_list@ == list@.subrange(0, n as int).reverse().add(list@.subrange(n as int, index as int)),
                reversed_list.len() == index,
                list.len() == list@.len(),
        {
            reversed_list.push(list[index]);
            index += 1;
        }
        
        // Proof block for the final state after the loop
        proof {
            assert(index == list.len());
            assert(reversed_list@ == list@.subrange(0, n as int).reverse().add(list@.subrange(n as int, list.len() as int)));
        }

        reversed_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmprcrg4sva`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True