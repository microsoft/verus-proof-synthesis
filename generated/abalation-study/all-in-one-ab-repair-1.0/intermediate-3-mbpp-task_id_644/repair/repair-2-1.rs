
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn is_reverse(list: Seq<i32>, start: int, len: int) -> bool {
        len <= list.len() && forall |i: int| 0 <= i && i < len ==> list.index(start + len - 1 - i) == list.index(start + i)
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
                    forall|i: int| 0 <= i < index ==> reversed_list[i] == list[(n - 1) - i],
                    reversed_list@.len() == index as int,
                    reversed_list@ == list@.subrange(0, index as int).reverse(),
            {
                reversed_list.push(list[n - 1 - index]);
                index += 1;
            }
            while index < list.len() // Loop to append the remaining part
                invariant
                    list@.len() > 0,
                    0 <= n <= list@.len(),
                    n <= index <= list.len(),
                    reversed_list@.len() == index as int,
                    reversed_list@ == list@.subrange(0, n as int).reverse().add(list@.subrange(n as int, index as int)),
            {
                reversed_list.push(list[index]);
                index += 1;
            }
            reversed_list
        }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpaauaws73`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False