use vstd::prelude::*;

fn main() {
    // Write a python function to find the sublist having minimum length.

    assert_eq!(
        min_sublist(&(vec![vec![1], vec![1, 2], vec![1, 2, 3]])),
        &vec![1]
    );
    assert_eq!(
        min_sublist(&(vec![vec![1, 1], vec![1, 1, 1], vec![1, 2, 7, 8]])),
        &vec![1, 1]
    );
    assert_eq!(
        min_sublist(&(vec![vec![1, 2, 3], vec![3, 4], vec![11, 12, 14]])),
        &vec![3, 4]
    );
}

verus! {

fn min_sublist(seq: &Vec<Vec<i32>>) -> (min_list: &Vec<i32>)
    requires
        seq.len() > 0,
    ensures
        forall|k: int| 0 <= k < seq.len() ==> min_list.len() <= #[trigger] (seq[k]).len(),
        exists|k: int| 0 <= k < seq.len() && min_list@ =~= #[trigger] (seq[k]@),
{
    let mut min_list = &seq[0];
    assert(min_list@ =~= seq[0]@);
    let mut index = 1;

    while index < seq.len()
        invariant
            0 <= index <= seq.len(),
            forall|k: int| 0 <= k < index ==> min_list.len() <= #[trigger] (seq[k]).len(),
            exists|k: int| 0 <= k < index && min_list@ =~= #[trigger] (seq[k]@),
    {
        if ((seq[index]).len() < min_list.len()) {
            min_list = &seq[index];
        }
        index += 1;
    }
    min_list
}

} // verus!
