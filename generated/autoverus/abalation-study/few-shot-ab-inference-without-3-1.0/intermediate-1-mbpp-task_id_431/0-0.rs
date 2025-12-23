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
            exists|found: bool| found == (exists|m: int, n: int| 0 <= m < i && 0 <= n < list2.len() && list1[m] == list2[n]) == result,
            list1.len() == old(list1).len(),
            list2.len() == old(list2).len(),
    {
        let mut j = 0;
        while j < list2.len()
            invariant
                0 <= j <= list2.len(),
                0 <= i < list1.len(),
                list1.len() == old(list1).len(),
                list2.len() == old(list2).len(),
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