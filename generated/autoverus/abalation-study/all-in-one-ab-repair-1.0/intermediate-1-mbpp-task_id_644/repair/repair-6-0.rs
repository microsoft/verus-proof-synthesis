
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
        }
        
        proof {
            assert_reversed_up_to_k_after_first_loop(list, n, index);
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
        }
        
        reversed_list
    }
    
    proof fn assert_reversed_up_to_k_after_first_loop(list: &Vec<i32>, n: usize, index: usize)
        requires
            list@.len() > 0,
            0 < n < list@.len(),
            0 <= index <= n,
        ensures
            list@.subrange(0, n as int).reverse().len() == index,
    {
        assert(list@.subrange(0, n as int).reverse().len() == n as int);
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp_57gbmhr`)
// 

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 3
// Safe: True