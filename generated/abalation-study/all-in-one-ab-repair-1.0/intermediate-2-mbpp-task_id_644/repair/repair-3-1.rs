
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
        let mut reversed_list = Vec::new();
        let mut index = 0;
        while index < n
            invariant
                list@.len() > 0,
                0 < n < list@.len(),
                0 <= index <= n,
                // Ensuring reversed_list matches the reverse of the sublist of `list`
                forall|i: int| 0 <= i < index ==> reversed_list[i as usize] == list[(n - 1 - i) as usize],
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
                0 < n < list@.len(),
                n <= index <= list.len(), // Updated invariant
                // Ensuring first part of reversed_list matches the reverse of the sublist of `list`
                forall|i: int| 0 <= i < n ==> reversed_list[i as usize] == list[(n - 1 - i) as usize],
                // Ensuring second part of reversed_list matches the latter part of the `list`
                forall|j: int| n <= j < index ==> reversed_list[j as usize] == list[j],
                reversed_list.len() == index,
                list.len() == list@.len(),
        {
            reversed_list.push(list[index]);
            index += 1;
        }
        reversed_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpu7rbjkp_`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: True