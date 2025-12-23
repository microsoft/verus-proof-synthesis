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
            exists|k: int, l: int| 
                0 <= k < i && 0 <= l < list2.len() && list1[k] == list2[l] ==> result,
    {
        let mut j = 0;
        while j < list2.len()
            invariant
                0 <= j <= list2.len(),
                forall|k: int| 
                    0 <= k < i ==> exists|l: int| 0 <= l < list2.len() && list1[k] == list2[l] ==> result,
                forall|l: int| 
                    0 <= l < j ==> exists|k: int| 0 <= k < i && list1[k] == list2[l] ==> result,
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