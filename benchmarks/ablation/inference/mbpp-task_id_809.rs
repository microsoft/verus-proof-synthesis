use vstd::prelude::*;

fn main() {}

verus! {

fn is_smaller(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    requires
        arr1.len() == arr2.len(),
    ensures
        result == (forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]),
{
    let mut index = 0;
    while index < arr1.len() {
        if arr1[index] <= arr2[index] {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
