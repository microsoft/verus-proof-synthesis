
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
            1 <= index <= seq.len(),
            1 <= seq.len(),
            exists|k: int| 0 <= k < index && min_list@ =~= # [trigger] (seq[k]@),
            exists|m: int| 0 <= m < index && min_list@ =~= # [trigger] (seq[m]@),
            forall|k: int| 0 <= k < index ==> min_list.len() <= # [trigger] (seq[k]).len(), // Modified to cover every element in the range because seq is not modified in the loop
            forall|k: int| 1 <= k < index ==> min_list.len() <= # [trigger] (seq[k]).len(), // Modified to cover every element in the range because seq is not modified in the loop
            index <= seq.len(),
            min_list.len() <= seq[0].len(),
            seq.len() > 0,
            seq.len() == seq.len(), // Invariant for length of seq
    {
        if ((seq[index]).len() < min_list.len()) {
            min_list = &seq[index];
        }
        index += 1;
    }
    min_list
}

} // verus!
// Score: (0, 1)
// Safe: True