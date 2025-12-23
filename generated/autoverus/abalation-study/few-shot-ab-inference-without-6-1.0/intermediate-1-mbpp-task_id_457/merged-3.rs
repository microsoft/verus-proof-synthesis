use vstd::prelude::*;
fn main() {}
verus! {

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
            forall|k: int| 0 <= k < index ==> min_list.len() <= (seq[k]).len(),
            1 <= index <= seq.len(),
            1 <= seq.len(),
            forall|j: int|
                0 <= j < index ==> (if min_list.len() == # [trigger] seq[j].len() {
                    min_list@ =~= # [trigger] seq[j]@
                } else {
                    true
                }),
            forall|j: int| 0 <= j < index ==> min_list.len() <= # [trigger] seq[j].len(),
            min_list.len() <= seq[0].len(),
    {
        if ((seq[index]).len() < min_list.len()) {
            min_list = &seq[index];
        }
        index += 1;
    }
    min_list
}

} // verus!


// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2