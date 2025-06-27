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
            index <= arr.len(),
            arr.len() == old(arr).len(),
	    forall |j: int| 0 <= j < index ==> ((j % 2) == (arr[j] % 2)),
    {
        if ((index % 2) != (arr[index] % 2)) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1