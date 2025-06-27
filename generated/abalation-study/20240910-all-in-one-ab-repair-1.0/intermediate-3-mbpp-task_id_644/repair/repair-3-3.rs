
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn is_reverse(list: Seq<int>, start: int, len: int) -> bool {
        len <= list.len() && forall |i: int| 0 <= i && i < len ==> list[start + len - 1 - i] == list[start + i]
    }

    fn reverse_to_k(list: &Vec<i32>, n: usize) -> Vec<i32>
        requires
            list@.len() > 0,
            0 < n < list@.len(),
        ensures
            result ==
                list@.subrange(0, n as int).reverse().add(
                    list@.subrange(n as int, list.len() as int)
                ),
    {
        let mut reversed_list = vec![];
        let mut index = 0;

        // Loop to reverse the first part
        while index < n
            invariant
                list@.len() > 0,
                0 < n < list@.len(),
                0 <= index <= n,
                reversed_list@.len() == index as int,
                is_reverse(reversed_list@, 0, index as int).implies(
                    reversed_list@ == list@.subrange(0, index as int).reverse()
                ),
                forall|i: int| 0 <= i < index ==> reversed_list[i] == list[(n - 1) as usize - i],
                list.len() == list@.len(),
        {
            reversed_list.push(list[n - 1 - index]);
            index += 1;
        }

        index = n;
        // Loop to append remaining part
        while index < list.len()
            invariant
                list@.len() > 0,
                0 <= n < list@.len(),
                0 <= index <= list.len(),
                is_reverse(reversed_list@.subrange(0, n as int), 0, n as int),
                reversed_list@.subrange(0, n as int) == list@.subrange(0, n as int).reverse(),
                reversed_list@.subrange(n as int, index as int) == list@.subrange(n as int, index as int),
                reversed_list@.len() == index as int,
                list.len() == list@.len(),
        {
            reversed_list.push(list[index]);
            index += 1;
        }

        return reversed_list;
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpm4vdasq2`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False