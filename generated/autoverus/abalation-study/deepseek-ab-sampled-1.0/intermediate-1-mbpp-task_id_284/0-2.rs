

use vstd::prelude::*;

fn main() {}

verus! {

fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)),
{
    let mut index = 0;
    while (index < arr.len())
        invariant 
            index <= arr.len(),
            forall |k: int| 0 <=k < index ==> ((arr[k] == element) as bool == true),
    {
        if arr[index] != element {
            return false;
        }
        index += 1;

        proof {
            assert((!((arr[index] != element) as bool)) as bool == true);
        }
    }
    true
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7