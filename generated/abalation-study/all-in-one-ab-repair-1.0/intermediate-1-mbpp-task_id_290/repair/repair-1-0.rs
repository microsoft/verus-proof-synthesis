
use vstd::prelude::*;
fn main() {}

verus! {
    fn max_length_list(seq: &Vec<Vec<i32>>) -> (max_list: &Vec<i32>)
        requires
            seq.len() > 0,
        ensures
            forall|k: int| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] (seq[k]).len(),
            exists|k: int| 0 <= k < seq.len() && max_list@ == #[trigger] (seq[k]@),
    {
        let mut max_list = &seq[0];
        let mut index = 1;
        while index < seq.len()
            invariant
                0 <= index <= seq.len(),
                exists|m: int| 0 <= m < index && max_list@ == #[trigger] (seq[m]@),
                forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] (seq[k]).len(),
                seq.len() > 0,
        {
            if ((seq[index]).len() > max_list.len()) {
                max_list = &seq[index];
            }
            index += 1;
        }
        proof {
            // Ensure the post-condition before returning
            assert(forall|k: int| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] (seq[k]).len());

            let k: int = (0usize..seq.len()).find(|&i| max_list as *const _ == &seq[i] as *const _).unwrap() as int;
            assert(k < seq.len());
            assert(max_list@ == #[trigger] (seq[k]@));
        }
        max_list
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpzo4hye1p`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False