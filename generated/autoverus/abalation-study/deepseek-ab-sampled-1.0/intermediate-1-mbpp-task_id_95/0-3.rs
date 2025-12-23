

use vstd::prelude::*;

fn main() {}

verus! {

fn smallest_list_length(list: &Vec<Vec<i32>>) -> (min: usize)
    requires
        list.len() > 0,
    ensures
        min >= 0,
        forall|i: int| 0 <= i < list.len() ==> min <= list[i].len(),
        exists|i: int| 0 <= i < list.len() && min == list[i].len(),
{
    let mut min = list[0].len();
    let mut index = 1;
    while (index < list.len())
        invariant
            index <= list.len(),
            min >=0,
            // For all vectors processed so far, min is less than or equal to their length
            forall|i: int| 0 <= i < index ==> min <= list[i].len(),
            // There exists at least one vector with length equal to min
            exists|i: int| 0 <= i < index && min == list[i].len(),
    {
        if (&list[index]).len() < min {
            min = (&list[index]).len();
        }
        index += 1;
    }
    min
}

} // verus!
// is safe: False
// Score: Compilation Error: False, Verified: 2, Errors: 0, Verus Errors: 0