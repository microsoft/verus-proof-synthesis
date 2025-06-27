use vstd::prelude::*;
fn main() {}

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
    while index < list.len() {
        new_list.push(list[index]);
        index += 1;
    }
    let mut index = 0;
    while index < n {
        new_list.push(list[index]);
        index += 1;
    }
    new_list
}

} // verus!
