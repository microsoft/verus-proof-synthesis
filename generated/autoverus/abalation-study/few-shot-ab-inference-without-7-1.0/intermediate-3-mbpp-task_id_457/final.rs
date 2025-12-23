
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn min_sublist(seq: &Vec<Vec<i32>>) -> (min_list: &Vec<i32>)
    requires
        seq.len() > 0,
    ensures
        forall|k: int| 0 <= k < seq.len() ==> min_list.len() <= # [trigger] (seq[k]).len(),
        exists|k: int| 0 <= k < seq.len() && min_list@ =~= # [trigger] (seq[k]@),
{
    let mut min_list = &seq[0];
    let mut index = 1;
    while index < seq.len()
        invariant
            0 <= index <= seq.len(),
            exists|k: int| 0 <= k < index && min_list@ =~= # [trigger] (seq[k]@),
            forall|j: int| 0 <= j < index ==> min_list.len() <= # [trigger] (seq[j]).len(),
            forall|k: int| 0 <= k < seq.len() ==> min_list.len() <= # [trigger] (seq[k]).len(), // The array `seq` is not modified in the loop, hence this invariant covers every element in the array.
            index <= seq.len(),
            seq.len() > 0,
            seq.len() == seq.len(),
    {
        if ((seq[index]).len() < min_list.len()) {
            min_list = &seq[index];
        }
        index += 1;
    }
    min_list
}

} // verus!
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2