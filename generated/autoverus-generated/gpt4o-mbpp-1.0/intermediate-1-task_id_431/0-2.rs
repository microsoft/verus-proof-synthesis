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
            exists|ri: int, rj: int|
                0 <= ri < i && 0 <= rj < list2.len() && list1[ri] == list2[rj]
                ==> result == true,
    {
        let mut j = 0;
        while j < list2.len()
            invariant
                0 <= j <= list2.len(),
                exists|ri: int, rj: int|
                    0 <= ri < i && 0 <= rj < list2.len() && list1[ri] == list2[rj]
                    ==> result == true,
                exists|ri: int, rj: int|
                    ri == i && 0 <= rj < j && list1[ri] == list2[rj]
                    ==> result == true,
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3