
use vstd::prelude::*;
fn main() {}

verus! {

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
            forall|i: int|
                0 <= i < index ==> reversed_list@.index(i) == list@.index((n as int - 1) - i),
            reversed_list@.len() == index as int,
    {
        reversed_list.push(list[n - 1 - index]);
        index += 1;
    }

    while index < list.len()
        invariant
            list@.len() > 0,
            0 < n < list@.len(),
            n <= index <= list@.len(),
            forall|i: int|
                0 <= i < n ==> reversed_list@.index(i) == list@.index((n as int - 1) - i),
            forall|j: int|
                n <= j < index as int ==> reversed_list@.index(j) == list@.index(j),
            reversed_list@.len() == index as int,
    {
        reversed_list.push(list[index]);
        index += 1;
    }

    reversed_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp9z6ivi1h`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: False