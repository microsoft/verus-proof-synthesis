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
            index <= arr.len(),
            arr.len() <= arr.len(), // trivial invariant for maintaining the length condition
            !result ==> (forall|i: int| 0 <= i < index ==> arr[i] != k), // if result is false up to now, k is not in the scanned portion
    {
        if (arr[index] == k) {
            return true;
        }
        index += 1;
    }
    false
}

} // verus!

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1