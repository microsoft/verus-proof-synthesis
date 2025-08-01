
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
            reversed_list.len() == index,
            list.len() == list@.len(),
            forall|i: int| 0 <= i < index ==> reversed_list[i as usize] == list[(n - 1 - i) as usize],
    {
        reversed_list.push(list[n - 1 - index]);
        index += 1;
    }
    proof {
        assert(reversed_list@ == list@.subrange(0, n as int).reverse());
    }
    
    while index < list.len()
        invariant
            list@.len() > 0,
            0 < n < list@.len(),
            n <= index <= list@.len(),
            reversed_list.len() == index,
            list.len() == list@.len(),
            reversed_list@.subrange(0, n as int) == list@.subrange(0, n as int).reverse(),
            reversed_list@.subrange(n as int, index as int) == list@.subrange(n as int, index as int),
    {
        reversed_list.push(list[index]);
        index += 1;
    }
    reversed_list
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmphamj24cd`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False