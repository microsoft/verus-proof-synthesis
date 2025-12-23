
use vstd::prelude::*;
fn main() {}

verus! {
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
        while index < n
            invariant
                list@.len() > 0,
                0 < n < list@.len(),
                0 <= index <= n,
                forall|i: int| 0 <= i < index ==> reversed_list@[i] == list@[(n - 1 - i as int) as usize],
                reversed_list@.len() == index as int,
                reversed_list@.len() == reversed_list.len() as int,
                forall|j: int| 0 <= j < reversed_list@.len() ⇔ reversed_list@.index(j) == list@.index((n - 1 - j) as int),
        {
            reversed_list.push(list[n - 1 - index]);
            index += 1;
        }
        index = n;
        while index < list.len()
            invariant
                list@.len() > 0,
                0 <= n < list.len(),
                0 < n < list@.len(),
                n <= index <= list.len(),
                forall|i: int| 0 <= i < n ==> reversed_list@[i] == list@[(n - 1 - i as int) as usize],
                forall|j: int| n <= j < index as int == reversed_list@[j] == list@[j],
                reversed_list@.index(n as int) == list@.index(n as int),
                reversed_list@.len() == index as int,
                reversed_list@.len() == reversed_list.len() as int,
        {
            reversed_list.push(list[index]);
            index += 1;
        }
        reversed_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp1bugt5z6`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False