
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
            0 < n < list@.len(),
            0 <= index <= n,
            reversed_list@ == list@.subrange(0, index as int).reverse(),
            reversed_list.len() == index,
            list.len() == list@.len(),
    {
        reversed_list.push(list[n - 1 - index]);
        index += 1;
    }

    index = n;
    while index < list.len()
        invariant
            n <= index <= list@.len(),
            reversed_list@ == list@.subrange(0, n as int).reverse().add(list@.subrange(n as int, index as int)),
            reversed_list.len() == index,
            list.len() == list@.len(),
    {
        reversed_list.push(list[index]);
        index += 1;
    }
    reversed_list
}

} // verus!

Let me know if there's any specific issue you're trying to resolve so I can assist further. If there is a configuration or environment issue, you should check your Rust toolchain, Verus, and how you run scripts to ensure there are no conflicting filenames or inputs. 

For running Verus, you typically run the verifier with:

sh
verus hhhh.rs


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpq8bn7i05`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False