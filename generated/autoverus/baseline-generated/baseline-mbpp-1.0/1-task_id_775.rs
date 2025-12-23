use vstd::prelude::*;

fn main() {}

verus! {

fn is_odd_at_odd_index(arr: &Vec<usize>) -> (result: bool)
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
{
    let mut index = 0;
    
    while index < arr.len()
    invariant
        0 <= index <= arr.len(),
        forall |i: int| 0 <= i < index ==> (i % 2) == (arr[i] % 2),
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