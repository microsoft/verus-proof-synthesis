
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
            forall|i: int| 0 <= i < index ==> reversed_list[i as usize] == list[(n - 1) - i as usize],
            reversed_list.len() == index,
    {
        reversed_list.push(list[n - 1 - index]);
        index += 1;
    }

    // Correct the loop invariant for the second loop
    while index < list.len()
        invariant
            list@.len() > 0,
            0 < n < list@.len(),
            n <= index <= list.len(),
            forall|i: int| 0 <= i < n ==> reversed_list[i as usize] == list[(n - 1) - i as usize],
            forall|j: int| n <= j < index ==> reversed_list[j as usize] == list[j],
            reversed_list.len() == index,
    {
        reversed_list.push(list[index]);
        index += 1;
    }
    
    // Ensure the final ensures clause holds
    proof {
        let pre_reversed = list@.subrange(0, n as int).reverse();
        let post_list = list@.subrange(n as int, list.len() as int);
        assert(reversed_list@ == pre_reversed.add(post_list));
    }
    reversed_list
}

} // verus!



// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp10oxp7xo`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False