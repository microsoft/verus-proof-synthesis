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
            i <= list1.len(),
            exists|res: bool| res == (exists|i1: int, j: int|
                0 <= i1 < list1.len() && 0 <= j < list2.len() && list1[i1] == list2[j]),
            forall|i2: int| 0 <= i2 < i ==> exists|j: int|
                0 <= j < list2.len() && list1[i2] == list2[j],
    {
        let mut j = 0;
        
        while j < list2.len()
            invariant
                j <= list2.len(),
                exists|res: bool| res == (exists|i1: int, j1: int|
                    0 <= i1 < list1.len() && 0 <= j1 < list2.len() && list1[i1] == list2[j1]),
                forall|j2: int| 0 <= j2 < j ==> list1[( i ) as int] != list2[j2],
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

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1