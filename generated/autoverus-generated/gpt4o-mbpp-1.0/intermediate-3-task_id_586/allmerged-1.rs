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
    while index < list.len()
        invariant
            0 < n < list@.len(),
            0 < n < list.len(),
            index <= list.len(),
            list@.len() > 0,
            n <= index <= list.len(),
            list.len() > 0,
            new_list@ == list@.subrange(n as int, index as int),
    {
        new_list.push(list[index]);
        index += 1;
    }
    let mut index = 0;
    while index < n
        invariant
            0 < n < list@.len(),
            0 <= index <= n,
            0 < n < list.len(),
            index <= n,
            list@.len() > 0,
            new_list@ == list@.subrange(n as int, list@.len() as int).add(
                list@.subrange(0, index as int),
            ),
            list.len() > 0,
            new_list@ == list@.subrange(n as int, list.len() as int).add(
                list@.subrange(0, index as int),
            ),
    {
        new_list.push(list[index]);
        index += 1;
    }
    new_list
}

} // verus!


// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 6