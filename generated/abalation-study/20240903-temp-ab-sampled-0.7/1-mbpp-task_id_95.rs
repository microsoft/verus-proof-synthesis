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
            0 <= index <= list.len(),
            min >= 0,
            exists|j: int| 0 <= j < index && min == #[trigger] list[j].len(),
            forall|k: int| 0 <= k < index ==> min <= #[trigger] list[k].len(),
    {
        if (&list[index]).len() < min {
            min = (&list[index]).len();
        }
        index += 1;
    }
    min
}

} // verus!
// Score: (2, 0)
// Safe: True