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
            n <= index <= list.len(),
            new_list.len() == index - n,
            forall|i: int| 0 <= i < new_list.len() ==> new_list@[i] == list@[(n as int + i) as int],
    {
        new_list.push(list[index]);
        index += 1;
    }

    let mut index = 0;

    while index < n
        invariant 
            0 <= index <= n,
            new_list.len() == list.len() - n + index,
            forall |i: int| 0 <= i < (list.len() - n) as int ==> new_list@[i] == list@[(n as int + i) as int],
            forall |i: int| (list.len() - n) as int  <= i <  new_list.len() as int ==> new_list@[i] == list@[(i - (list.len() - n)as int) as int],
    {
        new_list.push(list[index]);
        index += 1;
    }

    new_list
}

} // verus!
// Score: (1, 3)
// Safe: True