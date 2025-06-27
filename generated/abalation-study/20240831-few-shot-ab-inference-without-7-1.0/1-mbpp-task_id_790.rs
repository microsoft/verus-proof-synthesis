use vstd::prelude::*;

fn main() {}

verus! {

fn is_even_at_even_index(arr: &Vec<usize>) -> (result: bool)
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            index <= arr.len(),
            forall|j: int| 0 <= j < index ==> ((j % 2) == (arr[j] % 2)),
    {
        if ((index % 2) != (arr[index] % 2)) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// Score: (2, 0)
// Safe: True