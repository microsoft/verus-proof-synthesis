
use vstd::prelude::*;
fn main() {}

verus! {

    spec fn is_max_length(list: &Vec<i32>, seq: &Vec<Vec<i32>>, index: uint) -> bool {
        forall|k: uint| 0 <= k < index ==> list.len() >= #[trigger] seq[k].len()
    }

    fn max_length_list(seq: &Vec<Vec<i32>>) -> (max_list: &Vec<i32>)
        requires
            seq.len() > 0,
        ensures
            forall|k: uint| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] (seq[k]).len(),
            exists|k: uint| 0 <= k < seq.len() && max_list@ =~= #[trigger] (seq[k]@),
    {
        let mut max_list = &seq[0];
        let mut index = 1;

        while index < seq.len()
            invariant
                0 <= index <= seq.len(),
                exists|m: uint| 0 <= m < index && max_list@ =~= #[trigger] (seq[m]@),
                is_max_length(max_list, seq, index),
                seq.len() > 0,
        {
            if (seq[index]).len() > max_list.len() {
                max_list = &seq[index];
            }
            index += 1;
        }
        max_list
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpv_vb4_78`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: False