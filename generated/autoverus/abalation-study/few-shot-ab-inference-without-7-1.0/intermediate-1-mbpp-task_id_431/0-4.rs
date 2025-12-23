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
            exists|ii: int, jj: int| 0 <= ii < i && 0 <= jj < list2.len() && list1[ii] == list2[jj] ==>
            exists|i: int, j: int| 0 <= i < ii && 0 <= j < list2.len() && (list1[i] == list2[j]),
    {
        let mut j = 0;
        while j < list2.len()
            invariant
                j <= list2.len(),
                exists|ii: int, jj: int| 0 <= ii < list1.len() && 0 <= jj < j && list1[ii] == list2[jj] ==>
                exists|i: int, j: int| 0 <= i < list1.len() && 0 <= j < jj && list1[i] == list2[j],
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
// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 6