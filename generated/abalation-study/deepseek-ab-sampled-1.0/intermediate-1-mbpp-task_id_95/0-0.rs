
use vstd::prelude::*;

fn main() {}

verus! {

fn smallest_list_length(list: &Vec<Vec<i32>>) -> (min: usize)
    requires
        list.len() > 0,
    ensures
        min >= 0,
        forall|i: int| 0 <= i < list.len() ==> min <= #[trigger] list[i].len(),
        exists|i: int| 0 <= i < list.len() && min == #[trigger] list[i].len(),
{
    let mut min = list[0].len();
    let mut index = 1;
    
    while index < list.len()
        invariant
            // The loop invariant ensures that for all sublists up to the current index,
            // `min` holds the smallest length found so far.
            index <= list.len(),
            min < list[index - 1].len(),
            // The invariant to support loop progress and state
            // forall |i: int| 0 <= i < index ==> min <= list[i].len(),
            forall|i: int| 0 <= i < index ==> min <= list[i].len(),
            min >= 0,
    {
        if (&list[index]).len() < min {
            min = (&list[index]).len();
        }
        index += 1;
    }
    
    min
}

} // verus!

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3