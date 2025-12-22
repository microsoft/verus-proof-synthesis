use vstd::prelude::*;

fn main() {
    // Write a function in Rust to find the length of the smallest list in a list of lists.

    assert_eq!(smallest_list_length(&(vec![vec![1], vec![1, 2]])), 1);
    assert_eq!(
        smallest_list_length(&(vec![vec![1, 2], vec![1, 2, 3], vec![1, 2, 3, 4]])),
        2
    );
    assert_eq!(
        smallest_list_length(&(vec![vec![3, 3, 3], vec![4, 4, 4, 4]])),
        3
    );
}

verus! {

fn smallest_list_length(list: &Vec<Vec<i32>>) -> (min: usize)
    requires
        list.len() > 0,
    ensures
        min >= 0,
        forall|i: int| 0 <= i < list.len() ==> min <= #[trigger] list[i].len(),
        exists|i: int| 0 <= i < list.len() && min == #[trigger] list[i].len(),
{
    let mut min = list[0].len();

    let mut index = 1;
    while index < list.len()
        invariant
            0 <= index <= list.len(),
            forall|k: int| 0 <= k < index ==> min <= #[trigger] list[k].len(),
            exists|k: int| 0 <= k < index && min == #[trigger] list[k].len(),
    {
        if (&list[index]).len() < min {
            min = (&list[index]).len();
        }
        index += 1;
    }
    min
}

} // verus!
