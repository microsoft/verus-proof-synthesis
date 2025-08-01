
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::proof_blk]
    #[verifier::loop_invariant]
    #[verifier::spec_fn]
    proof fn is_reverse(list: Vec<int>, start: int, len: int) -> bool {
        len <= list.len() && forall |i: int| 0 <= i && i < len ==> list[start + len - 1 - i] == list[start + i]
    }

    #[verifier::loop_isolation(false)]
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
            while index < n // Loop to reverse the first part
                invariant
                    list@.len() > 0,
                    0 < n < list@.len(),
                    0 <= index <= n,
                    forall|i: int| 0 <= i < index ==> reversed_list[i] == list[(n - 1) as usize - i as usize],
                    list.len() == list@.len(),
                    reversed_list@.len() == index as int,
            {
                reversed_list.push(list[(n - 1) - index]);
                index += 1;
            }
            while index < list.len() // Loop to append the remaining part
                invariant
                    list@.len() > 0,
                    0 <= n < list.len(),
                    0 < n < list@.len(),
                    forall|i: int| 0 <= i < n ==> reversed_list[i] == list[(n - 1) as usize - i as usize],
                    forall|j: int| n <= j < index ==> reversed_list[j] == list[j],
                    list.len() == list@.len(),
                    reversed_list@.len() == index as int,
            {
                reversed_list.push(list[index]);
                index += 1;
            }
            reversed_list
        }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp3r9r77q3`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False