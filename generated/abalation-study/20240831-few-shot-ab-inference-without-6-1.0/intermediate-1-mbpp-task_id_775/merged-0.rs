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
            arr.len() < 1000,
            forall|i: int| 0 <= i < index ==> ((i % 2) == (arr[i] % 2)),
            index <= arr.len(),
    {
        if ((index % 2) != (arr[index] % 2)) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!


// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1