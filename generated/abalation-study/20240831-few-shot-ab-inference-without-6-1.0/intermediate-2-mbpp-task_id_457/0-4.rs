use vstd::prelude::*;

fn main() {}

verus! {

fn min_sublist(seq: &Vec<Vec<i32>>) -> (min_list: &Vec<i32>)
    requires
        seq.len() > 0,
    ensures
        forall|k: int| 0 <= k < seq.len() ==> min_list.len() <= #[trigger] (seq[k]).len(),
        exists|k: int| 0 <= k < seq.len() && min_list@ =~= #[trigger] (seq[k]@),
{
    let mut min_list = &seq[0];
    let mut index = 1;

    while index < seq.len()
        invariant
            1 <= len (seq),
            min_list.len()  <= N,
            forall|k:int| 0< k < index ==> seq[k] == seq0[k],
    {
        if ((seq[index]).len() < min_list.len()) {
            min_list = &seq[index];
        }
        index += 1;
    }
    min_list
}
} // verus!
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3