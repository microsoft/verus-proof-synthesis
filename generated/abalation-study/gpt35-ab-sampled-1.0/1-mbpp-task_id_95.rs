
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
    while index < list.len()
        invariant
            0 < list.len(), // from pre-condition
            index <= list.len(), // keeping track of index to prevent out of bound access
            min >= 0,
            forall|i: int| 0 <= i < index ==> min <= list[i].len(), // for all indexes visited so far, min <= length of list[i]
            exists|i: int| 0 <= i < index && min == list[i].len(), // there exists an index visited so far whose length is equal to min
    {
        if list[index].len() < min {
            min = list[index].len();
        }
        index += 1;
    }
    min
}

} // verus!

// Score: (2, 0)
// Safe: False