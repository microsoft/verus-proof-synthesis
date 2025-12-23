
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
{
    let mut index = 0;
    proof {
        assert(forall|i: int| 0 <= i < arr.len() - 1 ==> arr[i as int] + 1 == arr[i + 1]);
    }
    while (index < arr.len() - 1)
        invariant
            0 <= index <= arr.len(),
            0 <= index < arr.len() - 1 ==> arr[index as int] + 1 == arr[index + 1],
    {
        if (arr[index] + 1 != arr[index + 1]) {
            return false;
        }
        index += 1;
    }
    proof {
        assert(forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> arr[i] + 1 == arr[j]);
    }
    true
}

}


//             0 <= index < arr.len() - 1 ==> arr[index as int] + 1 == arr[index + 1],
//   None: 0 <= index < arr.len() - 1 ==> arr[index as int] + 1 == arr[index + 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True