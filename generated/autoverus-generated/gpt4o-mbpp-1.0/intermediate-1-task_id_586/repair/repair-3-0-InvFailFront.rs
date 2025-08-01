use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)
    requires
        list@.len() > 0,
        0 < n < list@.len(),
    ensures
        new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
{
    let mut new_list = Vec::new();
    let mut index = n;
    proof {
        assert(list@.len() > 0);
        assert(0 < n < list@.len());
        assert(0 <= n < list.len());
        assert(index <= list.len());
        assert(list.len() == list.len());
        assert(new_list.len() == index - n);
        assert(new_list@ == list@.subrange(n as int, index as int));
        assert(forall |k: int| 0 <= k < list.len() ==> list[k] == list[k]);
    } // Added by AI
    while index < list.len()
        invariant
            list@.len() > 0,
            0 < n < list@.len(),
            0 <= n < list.len(),
            index <= list.len(),
            list.len() == list.len(),
            new_list.len() == index - n,
            new_list@ == list@.subrange(n as int, index as int),
            // No modification to the array 'list' in this loop
            forall |k: int| 0 <= k < list.len() ==> list[k] == list[k],
    {
        new_list.push(list[index]);
        index += 1;
    }
    let mut index = 0;
    proof {
        assert(new_list@ == list@.subrange(n as int, list.len() as int));
    } // Added by AI
    while index < n
        invariant
            list@.len() > 0,
            0 < n < list@.len(),
            0 <= n < list.len(),
            index <= n,
            list.len() == list.len(),
            new_list.len() == (list.len() - n + index),
            new_list@ == list@.subrange(n as int, list.len() as int).add(
                list@.subrange(0, index as int),
            ),
            // No modification to the array 'list' in this loop
            forall |k: int| 0 <= k < list.len() ==> list[k] == list[k],
    {
        new_list.push(list[index]);
        index += 1;
    }
    new_list
}

} // verus!

//             new_list@ == list@.subrange(n as int, list.len() as int).add(
//                 list@.subrange(0, index as int),
//             ),
//   None: new_list@ == list@.subrange(n as int, list.len() as int).add(                 list@.subrange(0, index as int),             )

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: True