
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
            if ((seq[index]).len() > max_list.len()) {
                max_list = &seq[index];
            }
            index += 1;

            proof {
                // Maintain invariants within the proof block of the loop body
                assert(0 <= index <= seq.len());
                assert(exists|m: int| 0 <= m < index && max_list@ =~= #[trigger] (seq[m]@));
                assert(forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] (seq[k]).len());
            }
        }

        proof {
            assert(forall|k: int| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] seq[k].len());
            assert(exists|k: int| 0 <= k < seq.len() && max_list@ =~= #[trigger] seq[k]@);
        }

        max_list
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpeu9xyjvp`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Safe: True