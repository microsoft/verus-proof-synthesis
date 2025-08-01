
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::proof_blk]
    #[verifier::loop_invariant]
    #[verifier::spec_fn]
    proof fn is_reverse(list: Vec<int>, start: int, len: int) -> bool {
        len <= list.len() && forall |i: int| 0 <= i && i < len ==> list[start + len - 1 - i] == list[start + i]
    }

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
                    // Ensure elements in the reversed_list follow the reverse indexing from list
                    forall|i: int| 0 <= i < index ==> reversed_list[i as usize] == list[(n - 1 - i) as usize],
                    reversed_list.len() == index,
                    reversed_list@.len() == index as int,
                    list.len() == list@.len(),
            {
                reversed_list.push(list[n - 1 - index]);
                index += 1;
            }
            while index < list.len() // Loop to append the remaining part
                invariant
                    list@.len() > 0,
                    0 <= index <= list.len(),
                    0 < n < list@.len(),
                    // Maintain the invariant for reversed section
                    forall|i: int| 0 <= i < n ==> reversed_list[i as usize] == list[(n - 1 - i) as usize],
                    // Ensure new elements follow the original list for the untouched segment
                    forall|j: int| n <= j < index ==> reversed_list[j as usize] == list[j as usize],
                    reversed_list.len() == index,
                    reversed_list@.len() == index as int,
                    list.len() == list@.len(),
            {
                reversed_list.push(list[index]);
                index += 1;
            }
            reversed_list
        }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp_j9tvhr1`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: False