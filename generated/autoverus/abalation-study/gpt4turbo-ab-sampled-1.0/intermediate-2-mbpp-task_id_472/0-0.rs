use vstd::prelude::*;

fn main() {}

verus! {

fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
{
    let mut index = 0;
    while (index < arr.len() - 1)
        invariant
            index + 1 <= arr.len(),
            forall |i: int, j: int| 
                (0 <= i < j < index + 1) && (j == i + 1) ==> (arr[i] + 1 == arr[j]),
    {
        if (arr[index] + 1 != arr[index + 1]) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 2