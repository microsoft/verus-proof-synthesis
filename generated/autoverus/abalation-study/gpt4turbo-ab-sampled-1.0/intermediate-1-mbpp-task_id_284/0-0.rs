use vstd::prelude::*;

fn main() {}

verus! {

fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[index] == element)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            forall |i: int| 0 <= i < index ==> (arr[i] == element),
    {
        if arr[index] != element {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1