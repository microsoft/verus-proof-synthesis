use vstd::prelude::*;

fn main() {}

verus! {

fn has_common_element(list1: &Vec<i32>, list2: &Vec<i32>) -> (result: bool)
    ensures
        result == (exists|i: int, j: int|
            0 <= i < list1.len() && 0 <= j < list2.len() && (list1[i] == list2[j])),
{
    let mut i = 0;
    let len1 = list1.len();
    let len2 = list2.len();

    while i < len1
        invariant 
            0 <= i <= len1,
            result == (exists|ii: int, jj: int|
                0 <= ii < i && 0 <= jj < len2 && (list1[ii] == list2[jj])),
    {
        let mut j = 0;
        while j < len2
            invariant 
                0 <= j <= len2,
                result == (exists|ii: int, jj: int|
                    0 <= ii < i && 0 <= jj < len2 && (list1[ii] == list2[jj])) ||
                    (exists|ii: int, jj: int|
                    ii == i && 0 <= jj < j && (list1[ii] == list2[jj])),
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
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2