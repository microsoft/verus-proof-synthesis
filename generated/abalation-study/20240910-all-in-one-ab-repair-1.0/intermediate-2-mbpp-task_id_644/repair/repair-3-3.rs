
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::spinoff_prover]

    spec fn reverse_correct(list: Seq<i32>, n: int, reversed_list: Seq<i32>) -> bool {
        reversed_list == list.subrange(0, n).reverse().add(list.subrange(n, list.len()))
    }

    fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
        requires
            list@.len() > 0,
            0 < n < list@.len(),
        ensures
            reverse_correct(list@, n as int, reversed_list@),
    {
        let mut reversed_list = Vec::new();
        let mut index = 0;
        while index < n
            invariant
                list@.len() > 0,
                0 < n < list@.len(),
                0 <= index <= n,
                reversed_list@ =~= list@.subrange(0, index).reverse(),
                reversed_list.len() == index,
        {
            reversed_list.push(list[n - 1 - index]);
            index += 1;
        }
        index = n;
        while index < list.len()
            invariant
                list@.len() > 0,
                0 < n < list@.len(),
                n <= index <= list.len(),
                reversed_list@ =~= list@.subrange(0, n).reverse().add(list@.subrange(n, index)),
                reversed_list.len() == index,
        {
            reversed_list.push(list[index]);
            index += 1;
        }
        reversed_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpawz9e4nz`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False