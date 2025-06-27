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
            forall|k: int| 0 <= k < seq.len() ==> seq[k].len() >= 0,
            exists|n: int| 0 <= n < index && min_list@ =~= (seq[n])@,
            1 <= index <= seq.len(),
            forall|k: int| 0 <= k < index ==> min_list.len() <= #[trigger] (seq[k]).len(),
    {
        if ((seq[index]).len() < min_list.len()) {
            min_list = &seq[index];
        }
        index += 1;
    }
    min_list
}

} // verus!
// Score: (2, 0)
// Safe: True