
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
            if (seq[index].len() > max_list.len()) {
                max_list = &seq[index];
                proof {
                    assert(max_lengths_exists_cond(seq@, max_list@, index+1)); // Proof step for existence invariant.
                }
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp8yzao0yl`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False