
use vstd::prelude::*;
fn main() {}
verus! {

fn has_common_element(list1: &Vec<i32>, list2: &Vec<i32>) -> (result: bool)
    ensures
        result == (exists|i: int, j: int|
            0 <= i < list1.len() && 0 <= j < list2.len() && (list1[i] == list2[j])),
{
    let mut i = 0;
    while i < list1.len()
        invariant
            0 <= i <= list1.len(),
            list1.len() == list1.len(),
            list2.len() == list2.len(),
            forall|m: int, n: int| 0 <= m < i && 0 <= n < list2.len() ==> list1[m] != list2[n],
    {
        let mut j = 0;
        while j < list2.len()
            invariant
                0 <= j <= list2.len(),
                list1.len() == list1.len(),
                list2.len() == list2.len(),
                forall|m: int, n: int|
                    0 <= m <= i && 0 <= n < j ==> (m == i ==> list1[m] != list2[n]),
                forall|n: int| 0 <= n < j ==> list1[(i) as int] != list2[n],
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

// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2