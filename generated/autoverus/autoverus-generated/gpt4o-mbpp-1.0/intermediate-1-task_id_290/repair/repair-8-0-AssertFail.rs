use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn max_length_list(seq: &Vec<Vec<i32>>) -> (max_list: &Vec<i32>)
    requires
        seq.len() > 0,
    ensures
        forall|k: int| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] (seq[k]).len(),
        exists|k: int| 0 <= k < seq.len() && max_list@ =~= #[trigger] (seq[k]@),
{
    let mut max_list = &seq[0];
    let mut index = 1;
    
    // Ensure initial state meets the intended invariants
    proof {
        // Correct initial state to match initial invariants
        assert(exists|m: int| m == 0 && max_list@ =~= #[trigger] (seq[m]@));
        assert(forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] (seq[k]).len());
    }
    
    while index < seq.len()
        invariant
            0 <= index <= seq.len(),
            exists|m: int| 0 <= m < index && max_list@ =~= #[trigger] (seq[m]@),
            forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] (seq[k]).len(),
            seq.len() > 0,
    {
        if ((seq[index]).len() > max_list.len()) {
            max_list = &seq[index];

            proof {
                // Update the invariant to reflect the change in max_list
                assert(exists|m: int| m == index && max_list@ =~= #[trigger] (seq[m]@));
            }
        }
        index += 1;
        proof {
            // Update invariants after checking the length
            assert(forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] (seq[k]).len());
            assert(exists|m: int| 0 <= m < index && max_list@ =~= #[trigger] (seq[m]@));
        }
    }

    proof {
        assert(forall|k: int| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] (seq[k]).len());
    }

    max_list
}

}

//         assert(exists|m: int| m == 0 && max_list@ =~= #[trigger] (seq[m]@));
//   assertion failed: exists|m: int| m == 0 && max_list@ =~= #[trigger] (seq[m]@)

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True