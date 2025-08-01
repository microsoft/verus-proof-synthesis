use vstd::prelude::*;

fn main() {}

verus! {

fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> number > arr[j],
    {
        if number <= arr[i] {
            return false;
        }
        i += 1;
    }
    true
}

} // verus!
// Score: (2, 0)
// Safe: True