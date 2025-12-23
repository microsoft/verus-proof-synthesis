
use vstd::prelude::*;fn main() {}verus! {spec fn subrange_concat<T>(list: Seq<T>, n: int) -> Seq<T> {
    list.subrange(n, list.len()).add(list.subrange(0, n))
}

fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        new_list@ == subrange_concat(list@, n as int),
{
    let mut new_list = Vec::new();
    let mut index = n;
    while index < list.len()
        invariant
            0 < n < list@.len(),
            list@.len() > 0,
            n <= index <= list.len(),
            new_list@ == list@.subrange(n as int, index as int),
            list.len() == old(list).len(), // Loop invariant specifying the length of the array
    {
        new_list.push(list[index]);
        index += 1;
    }
    let mut index = 0;
    while index < n
        invariant
            0 < n < list@.len(),
            0 <= index <= n <= list@.len(),
            list@.len() > 0,
            new_list@ == subrange_concat(list@, n as int).take(new_list.len() as int + 1),
            list.len() == old(list).len(), // Loop invariant specifying the length of the array
    {
        new_list.push(list[index]);
        index += 1;
    }
    proof {
        let list_seq = list@;
        let final_new_list = new_list@;
        assert(final_new_list == list_seq.subrange(n as int, list_seq.len()).add(list_seq.subrange(0, n as int)));
    }
    new_list
}}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpn5qc1fr_`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False