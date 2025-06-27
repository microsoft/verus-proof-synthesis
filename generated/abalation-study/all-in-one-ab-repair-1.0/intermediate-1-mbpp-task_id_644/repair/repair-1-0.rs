
use vstd::prelude::*;
fn main() {}

verus! {

spec! fn reverse_seq<T>(s: Seq<T>) -> Seq<T> {
        s.reverse()
}

spec! fn reversed_to_k<T: Copy>(list: Seq<T>, k: int) -> Seq<T> {
    list.subrange(0, k).reverse().add(list.subrange(k, list.len()))
}

#[verifier::verify]
fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        reversed_list@ == reversed_to_k(list@, n as int),
{
    let mut reversed_list = Vec::new();
    let mut index = 0;
    while index < n
        invariant
            list@.len() > 0,
            0 < n < list@.len(),
            0 <= index <= n,
            forall|i: int| 0 <= i < index ==> reversed_list@.index(i) == list@.index(n as int - 1 - i),
            reversed_list@.len() == index,
    {
        reversed_list.push(list[n - 1 - index]);
        index += 1;
    }
    index = n;
    while index < list.len()
        invariant
            list@.len() > 0,
            0 < n <= list@.len(),
            forall|i: int| 0 <= i < n ==> reversed_list@.index(i) == list@.index(n as int - 1 - i),
            forall|i: int| n <= i < index ==> reversed_list@.index(i) == list@.index(i),
            reversed_list@.len() == index,
    {
        reversed_list.push(list[index]);
        index += 1;
    }
    reversed_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpr5ptp3dc`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False