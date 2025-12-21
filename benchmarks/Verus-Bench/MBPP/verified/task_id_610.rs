use vstd::prelude::*;
fn main() {
    //Write a function in Rust which takes a list and returns a list with the same elements, but the k'th element removed.

    assert_eq!(
        remove_kth_element(&vec![1, 1, 2, 3, 4, 4, 5, 1], 3),
        [1, 1, 3, 4, 4, 5, 1]
    );
    assert_eq!(
        remove_kth_element(&vec![0, 0, 1, 2, 3, 4, 4, 5, 6, 6, 6, 7, 8, 9, 4, 4], 4),
        [0, 0, 1, 3, 4, 4, 5, 6, 6, 6, 7, 8, 9, 4, 4]
    );
    assert_eq!(
        remove_kth_element(&vec![10, 10, 15, 19, 18, 18, 17, 26, 26, 17, 18, 10], 5),
        [10, 10, 15, 19, 18, 17, 26, 26, 17, 18, 10]
    );
}

verus! {

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 < k < list@.len(),
    ensures
        new_list@ == list@.subrange(0, k - 1 as int).add(
            list@.subrange(k as int, list.len() as int),
        ),
{
    let mut new_list = Vec::new();
    let mut index = 0;
    while index < (k - 1)
        invariant
            0 <= index <= k - 1,
            0 < k < list@.len(),
            new_list@ =~= list@.subrange(0, index as int),
    {
        new_list.push(list[index]);
        index += 1;
    }
    let mut index = k;
    while index < list.len()
        invariant
            k <= index <= list.len(),
            new_list@ =~= list@.subrange(0 as int, k - 1 as int).add(
                list@.subrange(k as int, index as int),
            ),
    {
        new_list.push(list[index]);
        index += 1;
    }
    assert(new_list@ == list@.subrange(0, k - 1 as int).add(
        list@.subrange(k as int, list.len() as int),
    ));
    new_list
}

} // verus!
