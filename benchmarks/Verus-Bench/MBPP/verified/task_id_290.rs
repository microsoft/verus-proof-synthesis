use vstd::prelude::*;

fn main() {
    // Write a function in Rust to find the list of maximum length in a list of lists

    assert_eq!(
        max_length_list(
            &(vec![
                vec![0],
                vec![1, 3],
                vec![5, 7],
                vec![9, 11],
                vec![13, 15, 17]
            ])
        ),
        &vec![13, 15, 17]
    );
    assert_eq!(
        max_length_list(&(vec![vec![1], vec![5, 7], vec![10, 12, 14, 15]])),
        &vec![10, 12, 14, 15]
    );
    assert_eq!(
        max_length_list(&(vec![vec![5], vec![15, 20, 25]])),
        &vec![15, 20, 25]
    );
}

verus! {

fn max_length_list(seq: &Vec<Vec<i32>>) -> (max_list: &Vec<i32>)
    requires
        seq.len() > 0,
    ensures
        forall|k: int| 0 <= k < seq.len() ==> max_list.len() >= #[trigger] (seq[k]).len(),
        exists|k: int| 0 <= k < seq.len() && max_list@ =~= #[trigger] (seq[k]@),
{
    let mut max_list = &seq[0];
    assert(max_list@ =~= seq[0]@);
    let mut index = 1;

    while index < seq.len()
        invariant
            0 <= index <= seq.len(),
            forall|k: int| 0 <= k < index ==> max_list.len() >= #[trigger] (seq[k]).len(),
            exists|k: int| 0 <= k < index && max_list@ =~= #[trigger] (seq[k]@),
    {
        if ((seq[index]).len() > max_list.len()) {
            max_list = &seq[index];
        }
        index += 1;
    }
    max_list
}

} // verus!
