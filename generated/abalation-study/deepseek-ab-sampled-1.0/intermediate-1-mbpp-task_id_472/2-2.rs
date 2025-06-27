

use vstd::prelude::*;

fn main() {}

verus! {

fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    requires
        arr@.len() > 0,
        forall|i: int| 0 <= i < arr@.len() ==> (0 <= #[trigger] arr@.index(i) + 1 < i32::MAX),
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr@.len() && j == i + 1 ==> (arr@.index(i) + 1 == arr@.index(j))),
{
    let mut index = 0;
    while (index < arr@.len() - ( 1 ) as nat)
        invariant
            index <= arr@.len(),
            forall|i: int| 0 <= i < index ==> arr@.index(i) + 1 == arr@.index(i + 1),
            arr@.len() > 0,
            forall|i: int| 0 <= i < arr@.len() ==> (0 <= arr@.index(i) + 1 < i32::MAX),
    {
        if (arr@.index(index) + 1 != arr@.index(index + 1)) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4