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
            forall |j: int| 0 <= j < index ==> arr[j] != k,
            arr.len() == old(arr).len(),
    {
        if (arr[index] == k) {
            /*
            the invariant 0 <= j < index ==> arr[j] != k also implies for any index beyond the index value until index < arr.len().
            any other intermediary loops within bounded (0 to len of arr) ensure same does not hold.
            */
            return true;
        }
        index += 1;
    }
    false
}

} // verus!
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1