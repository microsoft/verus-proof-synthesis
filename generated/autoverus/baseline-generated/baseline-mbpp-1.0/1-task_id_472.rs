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
            // Preserving all the requirements and ensuring conditions
            0 <= index < arr.len(),
            forall |i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
            true == (forall|m: int, n: int|
                0 <= m < n < index + 1 && n == m + 1 ==> (arr[m] + 1 == arr[n])),
    {
        if (arr[index] + 1 != arr[index + 1]) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
// Score: (2, 0)
// Safe: True