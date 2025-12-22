use vstd::prelude::*;

fn main() {
    // Write a function in Rust that takes in two lists and replaces the last element of the first list with the elements of the second list.

    assert_eq!(
        replace_last_element(&vec![1, 3, 5, 7, 9, 10], &vec![2, 4, 6, 8]),
        [1, 3, 5, 7, 9, 2, 4, 6, 8]
    );
    assert_eq!(
        replace_last_element(&vec![1, 2, 3, 4, 5], &vec![5, 6, 7, 8]),
        [1, 2, 3, 4, 5, 6, 7, 8]
    );
    assert_eq!(
        replace_last_element(&vec![1, 2, 4, 6, 8], &vec![3, 5, 7, 9]),
        [1, 2, 4, 6, 3, 5, 7, 9]
    );
}

verus! {

fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)
    requires
        first.len() > 0,
    ensures
        replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
{
    let mut replaced_list = Vec::new();
    let first_end = first.len() - 1;
    let mut index = 0;

    while index < first_end
        invariant
            first_end == first.len() - 1,
            0 <= index <= first_end,
            replaced_list@ =~= first@.subrange(0, index as int),
    {
        replaced_list.push(first[index]);
        index += 1;
    }
    index = 0;
    while index < second.len()
        invariant
            0 <= index <= second.len(),
            replaced_list@ =~= first@.subrange(0, first.len() - 1).add(
                second@.subrange(0, index as int),
            ),
    {
        replaced_list.push(second[index]);
        index += 1;
    }
    assert(replaced_list@ =~= first@.subrange(0, first.len() - 1).add(second@));
    replaced_list
}

} // verus!
