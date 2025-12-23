
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn max_length_list(seq: &Vec<Vec<i32>>) -> (max_list: &Vec<i32>)
        requires
            seq.len() > 0,
        ensures
            forall |k: int| 0 <= k < seq.len() ==> max_list.len() >= #(seq[k].len()),
            exists |k: int| 0 <= k < seq.len() && max_list@ =~= #(seq[k]@),
    {
        let n = seq.len();
        let mut max_list = &seq[0];
        let mut index = 1;
        
        while index < n
            invariant
                0 <= index <= n,
                exists |m: int| 0 <= m < index && max_list@ =~= #(seq[m]@),
                forall |k: int| 0 <= k < index ==> max_list.len() >= #(seq[k].len()),
                seq.len() > 0,
        {
            if seq[index].len() > max_list.len() {
                max_list = &seq[index];
            }
            index += 1;

            // Establish invariant after mutation.
            proof {
                assert(0 <= index <= n);
                assert(seq.len() > 0);
                assert(forall |k: int| 0 <= k < index ==> max_list.len() >= #(seq[k].len()));
                assert(exists |m: int| 0 <= m < index && max_list@ =~= #(seq[m]@));
            }
        }
        
        // Establish final ensures
        proof {
            assert(forall |k: int| 0 <= k < seq.len() ==> max_list.len() >= #(seq[k].len()));
            assert(exists |k: int| 0 <= k < seq.len() && max_list@ =~= #(seq[k]@));
        }

        max_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpvr8pp6py`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False