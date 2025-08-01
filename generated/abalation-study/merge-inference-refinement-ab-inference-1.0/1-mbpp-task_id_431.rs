use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn has_common_element(list1: &Vec<i32>, list2: &Vec<i32>) -> (result: bool)
    ensures
        result == (exists|i: int, j: int|
            0 <= i < list1.len() && 0 <= j < list2.len() && (list1[i] == list2[j])),
{
    let mut i = 0;
    while i < list1.len()
        invariant
            0 <= i <= list1.len(),
            forall|x: int, y: int| 0 <= x < i && 0 <= y < list2.len() ==> list1[x] != list2[y],
            list1.len() == list1.len(),
            list2.len() == list2.len(),
    {
        let mut j = 0;
        while j < list2.len()
            invariant
                0 <= j <= list2.len(),
                forall|x: int| 0 <= x < j ==> list1[(i) as int] != list2[x],
                list1.len() == list1.len(),
                list2.len() == list2.len(),
        {
            if list1[i] == list2[j] {
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    false
}

} // verus!

// Score: (1, 0)
// Safe: True