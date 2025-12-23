use vstd::prelude::*;

fn main() {}

verus! {

fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            !exists|j: int| 0 <= j < index && arr[j] == k,
    {
        if arr[index] == k {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
// Score: (2, 0)
// Safe: False