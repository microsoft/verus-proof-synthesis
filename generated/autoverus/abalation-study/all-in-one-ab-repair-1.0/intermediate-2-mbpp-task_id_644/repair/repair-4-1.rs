
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::spinoff_prover]
    fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
        requires
            list@.len() > 0,
            0 < n < list@.len(),
        ensures
            reversed_list@ == list@.subrange(0, n as int).reverse().add(
                list@.subrange(n as int, list.len() as int),
            ),
    {
        // Create a mutable Vec to store the reversed list
        let mut reversed_list = Vec::new();
        let mut index = 0;

        // Reverse the first `n` elements and add them to `reversed_list`
        while index < n
            invariant
                list@.len() > 0,
                0 < n < list@.len(),
                0 <= index <= n,
                forall|i: int|
                    0 <= i < index ==> reversed_list[i as usize] == list[(n - 1 - i) as usize],
                reversed_list.len() == index,
                list.len() == list@.len(),
        {
            reversed_list.push(list[n - 1 - index]);
            index += 1;
        }

        // Continue adding the rest of the elements to `reversed_list`
        index = n;
        while index < list.len()
            invariant
                list@.len() > 0,
                0 < n < list@.len(),
                0 <= index <= list.len(),
                forall|i: int| 0 <= i < n ==> reversed_list[i as usize] == list[(n - 1 - i) as usize],
                forall|j: int| n <= j < index ==> reversed_list[j as usize] == list[j],
                reversed_list.len() == index,
                list.len() == list@.len(),
        {
            reversed_list.push(list[index]);
            index += 1;
        }

        // Final assertion to ensure the reversed_list meets the postcondition
        proof {
            // Range of reversed part
            let reversed_part = list@.subrange(0, n as int).reverse();
            // Range of unchanged part
            let unchanged_part = list@.subrange(n as int, list@.len());
            assert(reversed_list@ == reversed_part.add(unchanged_part));
        }

        reversed_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpbpry9xww`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: True