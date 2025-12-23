use vstd::prelude::*;
fn main() {}

verus! {

fn remove_kth_element(list: &Vec<i32>, k: usize) -> (new_list: Vec<i32>)
    requires
        list.len() > 0,
        0 <= k < list@.len(),
    ensures
        new_list@ == list@.subrange(0, k as int).add(
            list@.subrange((k + 1) as int, list.len() as int),
        ),
{
    let mut new_list = Vec::new();
    let mut index = 0;
    while index < k {
        new_list.push(list[index]);
        index += 1;
    }
    let mut index = k + 1;
    while index < list.len() {
        new_list.push(list[index]);
        index += 1;
    }
    new_list
}

} // verus!
// Score: (1, 2)
// Safe: False