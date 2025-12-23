
    use vstd::prelude::*;
    fn main() {}

    verus! {
        #[verifier::loop_isolation(false)]
        pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
            requires
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // elements are unique
            ensures
                forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // all elements in output are <= e and from v
                forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]), // all elements from v that are <= e are in result
        {
            let mut i: usize = 0;
            let vlen = v.len();
            let mut result: Vec<i32> = vec![];
            while (i < v.len())
                invariant
                    v.len() == vlen, // len of v does not change
                    result.len() <= i, // len of result is always <= i
                    forall|k: int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]), // all elements in v from 0 to i that are <= e are in result
                    forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]), // all elements in result are from v and <= e
                    i <= v.len(), // i is always within the range of v
                    forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // elements in v are unique
            {
                if (v[i] <= e) {
                    result.push(v[i]);
                }
                i = i + 1;
            }
            result
        }
    } // verus!

3. **Tool-Specific Advice**:

    - **Single Input File**: Based on the error message, make sure when running the tool to verify a single file. If running from a script or a build system, ensure only one Verus-specific `.rs` file is passed in each command.
    - **File Clean-Up**: Verify that no temporary or residual files are cluttering the workspace. The error indicates potential multiple files are causing a name clash.
    - **Debug Workflow**: If using an IDE or continuous integration setup to run Verus, inspect the command/makefile configuration for any errors concatenating filenames/paths.

4. **Running Verification**:

    - **Command Line**: Assuming you have Verus configured properly, a typical command to verify the file might resemble:
        verus your_filename.rs
        

// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpm7jmnqrq`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False