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
            exists|result: bool| result == (exists|i_int: int, j: int|
                0 <= i_int < i && 0 <= j < list2.len() && (list1[i_int] == list2[j])),
    {
        let mut j = 0;
        while j < list2.len()
            invariant
                0 <= j <= list2.len(),
                exists|result: bool| result == (exists|i_int: int, j_int: int|
                    0 <= i_int < i && 0 <= j_int < list2.len() && (list1[i_int] == list2[j_int])
                    || (0 <= i < list1.len() && 0 <= j_int < j && (list1[( i ) as int] == list2[j_int]))),
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