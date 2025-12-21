use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun1(x: &Vec<i32>) -> (max_index: usize)
    requires
        x.len() >= 1,
    ensures
        forall|k: int| 0 <= k < x.len() ==> x[max_index as int] >= x[k],
        max_index < x.len(),
{
    let mut max_index = 0;
    let mut i: usize = 1;
    while (i < x.len())
        invariant
            i <= x.len(),
            max_index < x.len(),
            forall|k: int| 0 <= k < i ==> x[max_index as int] >= x[k],
    {
        if x[i] > x[max_index] {
            max_index = i;
        }
        i = i + 1;
    }

    max_index
}

} // verus!
