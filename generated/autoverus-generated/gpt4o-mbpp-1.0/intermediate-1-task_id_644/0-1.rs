use vstd::prelude::*;
fn main() {}

verus! {

fn reverse_to_k(list: &Vec<i32>, n: usize) -> (reversed_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        reversed_list@ == list@.subrange(0, n as int).reverse().add(
            list@.subrange(n as int, list.len() as int),
        ),
{
    let mut reversed_list = Vec::new();
    let mut index = 0;
    while index < n
        invariant
            index <= n,
            reversed_list.len() == index,
            reversed_list@ == list@.subrange(0, index as int).reverse(),
    {
        reversed_list.push(list[n - 1 - index]);
        index += 1;
    }
    index = n;
    while index < list.len()
        invariant
            index <= list.len(),
            reversed_list.len() == index,
            reversed_list@ == list@.subrange(0, n as int).reverse().add(
                list@.subrange(n as int, index as int),
            ),
    {
        reversed_list.push(list[index]);
        index += 1;
    }
    reversed_list
}

} // verus!
// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3