
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    pub fn remove_all_greater(v: Vec<i32>, e: i32) -> Vec<i32>
        requires
            forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
        ensures
            forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall|k: int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
    {
        let mut i: usize = 0;
        let vlen = v.len();
        let mut result: Vec<i32> = vec![];
        while (i < v.len())
            invariant
                v.len() == vlen,
                result.len() <= i,
                forall|k: int| 0 <= k < i ==> v[k] <= e ==> result@.contains(v[k]),
                forall|k: int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
                i <= v.len(),
                forall|k1: int, k2: int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2], // Repeated invariant
        {
            if v[i] <= e {
                result.push(v[i]);
            }
            i = i + 1;
        }
        result
    }
}

### Checklist for Correct Environment Invocation:
- **Single Input File:** Ensure that Verus is invoked with no more than one input file. Check your build or run scripts to make sure only one file is provided.
- **Update Environment:** Make sure your Verus environment and related dependencies are up to date.
- **Correct File Paths:** Resolve any potential issues related to file paths in your development setup.

### Steps to Run and Verify:
1. **Compile and Run:**
   sh
   verus file_name.rs
   

// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpa91zt3il`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False