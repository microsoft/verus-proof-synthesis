
use vstd::prelude::*;

fn main() {}

verus! {

    spec fn max_lengths_forall_cond(seq: Seq<Seq<i32>>, max_list: Seq<i32>, index: int) -> bool {
        forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] seq[k].len()
    }
  
    spec fn max_lengths_exists_cond(seq: Seq<Seq<i32>>, max_list: Seq<i32>, index: int) -> bool {
        exists|m: int| 0 <= m < index && max_list =~= #[trigger] seq[m]
    }

    fn max_length_list(seq: &Vec<Vec<i32>>) -> (max_list: &Vec<i32>)
        requires
            seq.len() > 0,
        ensures
            forall|k: int| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] (seq[k]).len(),
            exists|k: int| 0 <= k < seq.len() && max_list@ =~= #[trigger] (seq[k]@),
    {
        let mut max_list = &seq[0];
        let mut index = 1;
        while index < seq.len()
            invariant
                0 <= index <= seq.len(),
                exists|m: int| 0 <= m < index && max_list@ =~= #[trigger] (seq[m]@),
                forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] (seq[k]).len(),
                seq.len() > 0,
        {
            if seq[index].len() > max_list.len() {
                max_list = &seq[index];
            }
            index += 1;
        }

        proof {
            assert(forall|k: int| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] seq[k].len());
            assert(exists|k: int| 0 <= k < seq.len() && max_list@ =~= #[trigger] seq[k]@);
        }

        max_list
    }
} // verus!

### Suggested Steps:
1. **Tool Runner Check**:
    - Ensure you're specifying only one input file properly when running the compiler/interpreter for the provided Rust Verus code.
    - If using an IDE with integration, ensure file paths are correctly referenced, and no multiple-input errors occur from misconfigurations.

2. **Environment Setup**:
    - Confirm that Verus and Rust compiler setup adheres to the necessary environment configurations.
    - Depending on your setup, rerun the command with specific flags to enable any higher value debugging or error verbosity if tools like `cargo`, `rustc`, or custom Verus tool commands are used.

3. **Version Compatibility**:
    - Ensure the versions of Rust, Verus, and any other tools are compatible and currently updated.

### Debugging:
1. **Single Command Run**:
    - Attempt run code files in isolated environments using minimalist commands so complex errors can be stripped out:
    sh
    cargo check --example example_name.rs
2. **Isolated Compilation**:
    - Compile/verus-check with single file input:
    sh
    rustc --verus yourfile.rs

3. **Verbosity Corection**:
    - Use flag:
    sh
    verus --multiple-errors 
    

// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp6jawdlnq`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6
// Safe: False