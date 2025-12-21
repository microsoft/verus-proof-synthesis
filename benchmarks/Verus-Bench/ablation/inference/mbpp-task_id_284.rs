use vstd::prelude::*;

fn main() {}

verus! {

fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)),
{
    let mut index = 0;
    while index < arr.len() {
        if arr[index] != element {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
