use vstd::prelude::*;
fn main() {
    //Write a function in Rust to split a list at the nth eelment and add the first part to the end.

    assert_eq!(
        split_and_append(&vec![12, 10, 5, 6, 52, 36], 2),
        [5, 6, 52, 36, 12, 10]
    );
    assert_eq!(split_and_append(&vec![1, 2, 3, 4], 1), [2, 3, 4, 1]);
    assert_eq!(
        split_and_append(&vec![0, 1, 2, 3, 4, 5, 6, 7], 3),
        [3, 4, 5, 6, 7, 0, 1, 2]
    );
}

verus! {

fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
{
    let mut new_list = Vec::new();
    let mut index = n;
    while index < list.len()
        invariant
            n <= index <= list.len(),
            list@.subrange(n as int, index as int) =~= new_list@,
    {
        new_list.push(list[index]);
        index += 1;
    }
    let mut index = 0;
    while index < n
        invariant
            0 < n < list@.len(),
            0 <= index <= n,
            new_list@ =~= list@.subrange(n as int, list@.len() as int).add(
                list@.subrange(0, index as int),
            ),
    {
        new_list.push(list[index]);
        index += 1;
    }
    new_list
}

} // verus!
