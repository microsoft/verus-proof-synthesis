use vstd::prelude::*;

fn main() {}

verus! {

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
            1 <= index <= seq.len(),
            max_list.len() >= seq[0].len(),
            forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] (seq[k]).len(),
            exists|k: int| 0 <= k < index && max_list@ =~= #[trigger] (seq[k]@),
    {
        if (seq[index]).len() > max_list.len() {
            max_list = &seq[index];
        }
        index += 1;
    }
    max_list
}

} // verus!
// Score: (2, 0)
// Safe: False