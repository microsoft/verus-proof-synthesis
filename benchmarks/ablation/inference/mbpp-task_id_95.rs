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
    while index < list.len() {
        if (&list[index]).len() < min {
            min = (&list[index]).len();
        }
        index += 1;
    }
    min
}

} // verus!
