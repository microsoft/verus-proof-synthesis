
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
                forall|i: int| 0 <= i < index ==> reversed_list[i] == list[(n - 1) as usize - i as usize],
                forall|j: int| 0 <= j < list.len() ==> (j < index ==> reversed_list[j as int] == list[(n - 1 - j) as int]),
                index <= n,
                reversed_list.len() == index,
                list.len() == list@.len(),
                reversed_list@.len() == index as int,
        {
            reversed_list.push(list[n - 1 - index]);
            index += 1;
        }

        while index < list.len()
            invariant
                list@.len() > 0,
                0 < n < list@.len(),
                0 <= index <= list@.len(),
                forall|i: int| 0 <= i < n ==> reversed_list[i] == list[(n - 1) as usize - i as usize],
                forall|j: int| 0 <= j < list.len() ==> (n <= j < index ==> reversed_list[j as int] == list[j as int]),
                index <= list.len(),
                reversed_list.len() == index,
                list.len() == list@.len(),
                reversed_list@.len() == index as int,
        {
            reversed_list.push(list[index]);
            index += 1;
        }
        reversed_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp4jjpn1hv`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2
// Safe: False