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
        assert(new_list@ == list@.subrange(n as int, n as int)); // Added by AI
    }
    while index < list.len()
        invariant
            0 < n < list@.len(),
            list@.len() > 0,
            n <= index <= list.len(),
            index <= list.len(),
            new_list@ == list@.subrange(n as int, index as int),
            list.len() == list.len(), // Loop invariant specifying the length of the array
    {
        new_list.push(list[index]);
        index += 1;
    }
    let mut idx = 0; // Renamed from index to idx to avoid shadowing
    while idx < n
        invariant
            0 < n < list@.len(),
            0 <= idx <= n,
            list@.len() > 0,
            idx <= n,
            new_list@ == list@.subrange(n as int, list@.len() as int).add(
                list@.subrange(0, idx as int),
            ),
            list.len() == list.len(), // Loop invariant specifying the length of the array
    {
        new_list.push(list[idx]);
        idx += 1;
    }
    new_list
}

} // verus!

//             new_list@ == list@.subrange(n as int, list@.len() as int).add(
//                 list@.subrange(0, index as int),
//             ),
//   None: new_list@ == list@.subrange(n as int, list@.len() as int).add(                 list@.subrange(0, index as int),             )

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: False