
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn is_subrange_reverse(a: Seq<i32>, n: int) -> bool {
        a.subrange(0, n).reverse().add(a.subrange(n, a.len())) == a
    }

    #[verifier::spinoff_prover]
    fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
        requires
            list@.len() > 0,
            0 < n < list@.len(),
        ensures
            is_subrange_reverse(list@, n as int),
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
                exists|rev: Seq<i32>| rev == list@.subrange(0, n as int).reverse().take(index as int) && 
                                      reversed_list@ == rev,
                reversed_list.len() == index,
                list.len() == list@.len(),
                reversed_list.len() == reversed_list@.len(),
        {
            reversed_list.push(list[n - 1 - index]);
            index += 1;
        }
        index = n;
        while index < list.len()
            invariant
                list@.len() > 0,
                0 < n < list@.len(),
                0 <= index <= list.len(),
                exists|rev: Seq<i32>| rev == list@.subrange(0, n as int).reverse() && 
                                      reversed_list@ == rev.add(list@.subrange(n as int, index as int)),
                reversed_list.len() == index,
                list.len() == list@.len(),
                reversed_list.len() == reversed_list@.len(),
        {
            reversed_list.push(list[index]);
            index += 1;
        }
        reversed_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpkwkyke0i`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False