
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
        requires
            list@.len() > 0,
            0 < n < list@.len(),
        ensures
            new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
    {
        let mut new_list = Vec::new();
        let mut index = n;
        while index < list.len()
            invariant
                0 < n < list@.len(),
                list@.len() > 0,
                n <= index <= list.len(),
                new_list@ == list@.subrange(n as int, index as int),
                list.len() == old(list).len(), // Loop invariant specifying the length of the array
        {
            new_list.push(list[index]);
            index += 1;
        }
        let mut index = 0;
        while index < n
            invariant
                0 < n < list@.len(),
                0 <= index <= n,
                list@.len() > 0,
                new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, index as int)),
                list.len() == old(list).len(), // Loop invariant specifying the length of the array
        {
            new_list.push(list[index]);
            index += 1;
        }
        new_list
    }
} // verus!

### Explanation:
1. **Invariants:**
   - Ensure `0 < n < list@.len()` and other constraints are maintained.
   - Conditions related to indices and the new list's concatenation state are verified.

2. **Maintaining Original List Length:**
   - Using `list.len() == old(list).len()` ensures the original list length remains unchanged during loops.

3. **Condition Clarification:**
   - Verified `n <= index <= list.len()` and `0 <= index <= n` facilitate correct loop termination and integrity of the operations.

### Command Invocation:
Ensure you run the Verus tool with the proper command and input file, for example:
sh
verus verifying_tool.rs


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpa7dtgxi4`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 10
// Safe: False