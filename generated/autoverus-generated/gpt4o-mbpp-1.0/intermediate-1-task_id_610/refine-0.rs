
use vstd::prelude::*;
fn main() {}
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
            forall|i: int| 0 <= i < index ==> new_list[i] == list[i],
            index < k,
            index <= k - 1,
            new_list.len() == index,
            new_list@.len() == index,
            list.len() > 0,
            0 < k < list@.len(),
    {
        new_list.push(list[index]);
        index += 1;
    }
    let mut index = k;
    while index < list.len()
        invariant
            forall|i: int| 0 <= i < k - 1 ==> new_list[i] == list[i],
            forall|i: int| k <= i < index ==> new_list[i - 1] == list[i],
            index <= list.len(),
            index >= k,
            k <= index <= list.len(),
            new_list.len() == index - 1,
            new_list@.len() == index - 1,
            list.len() > 0,
            0 < k < list@.len(),
    {
        new_list.push(list[index]);
        index += 1;
    }
    new_list
}

} // verus!
