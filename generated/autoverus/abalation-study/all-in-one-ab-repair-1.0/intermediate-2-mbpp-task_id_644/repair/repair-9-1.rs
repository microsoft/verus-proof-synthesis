
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
                exists|rev: Seq<i32>| 
                    rev == list@.subrange(0, n as int).reverse().take(index as int) &&
                    reversed_list@ == rev,
                reversed_list.len() == index,
                list.len() == list@.len(),
                reversed_list.len() == reversed_list@.len(),
        {
            reversed_list.push(list[n - 1 - index]);
            index += 1;
        }
        index = n;
        while index < list.len()
            invariant
                list@.len() > 0,
                0 < n < list@.len(),
                0 <= index <= list.len(),
                exists|rev: Seq<i32>| 
                    rev == list@.subrange(0, n as int).reverse() &&
                    reversed_list@ == rev.add(list@.subrange(n as int, index as int)),
                reversed_list.len() == index,
                list.len() == list@.len(),
                reversed_list.len() == reversed_list@.len(),
        {
            reversed_list.push(list[index]);
            index += 1;
        }
        reversed_list
    }
}

#### Checklist:
1. **File passing to verifier**:
   - Make sure you are passing the correct file and only one file to the verifier's command.

2. **Path / Directory**:
   - Ensure you're in the right directory or path from which the files are verifiable by the tool.

3. **Arguments Clean-Up**:
   - Verify the command with necessary arguments alone and no unwanted commas or filenames.

Here's a basic template command if certain tools follow the typical Rust compilation:

sh
verus yourfile.rs

This ensures your verifier reads only `yourfile.rs`.

Also, you may redirect specific errors and logs to troubleshoot better:

sh
verus yourfile.rs 2> error_log.txt


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpk3qrn86m`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: False