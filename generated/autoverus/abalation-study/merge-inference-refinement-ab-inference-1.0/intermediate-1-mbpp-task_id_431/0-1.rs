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
            forall |k: int| 0 <= k < i ==> !exists |j:int| 0 <= j < list2.len() && list1[k] == list2[j],
            list1.len() == old(list1).len(),
            list2.len() == old(list2).len(),
    {
        let mut j = 0;
        while j < list2.len()
            invariant
                j <= list2.len(),
                forall |m: int| 0 <= m < j ==> list1[( i ) as int] != list2[m],
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