
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
        let list_len = list.len(); // Ensure length is kept in a variable
        let mut index = 0;
        while index < n
            invariant
                list_len == list@.len(), // Maintain the original length
                0 < n < list_len,
                0 <= index <= n,
                reversed_list@ == list@.subrange(0, index as int).reverse(),
                reversed_list.len() == index,
                list.len() == list_len,
        {
            reversed_list.push(list[n - 1 - index]);
            index += 1;
        }
        index = n;
        while index < list_len
            invariant
                list_len == list@.len(), // Maintain the original length
                n <= index <= list_len,
                reversed_list@ == list@.subrange(0, n as int).reverse().add(list@.subrange(n as int, index as int)),
                reversed_list.len() == index,
                list.len() == list_len,
        {
            reversed_list.push(list[index]);
            index += 1;
        }
        reversed_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpzfqfhyvg`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: False