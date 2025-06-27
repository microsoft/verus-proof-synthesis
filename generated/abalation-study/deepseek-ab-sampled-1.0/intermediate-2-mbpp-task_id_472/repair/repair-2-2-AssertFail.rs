
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
    let n = arr.len();
    if n == 0 {
        return false;
    }
    let mut index = 0;
    while (index < n - 1)
        invariant
            0 <= index <= n - 1,
            n >= 1,
            forall|i: int, j: int| 0 <= i < j < index + 1 ==> (arr[i] + 1 == arr[j]),
            forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    {
        if (arr[index] + 1 != arr[index + 1]) {
            return false;
        }
        index += 1;
        proof {
            let old_index = index - 1;
            if old_index < 0 {
                continue;
            }
            assert(forall|i: int, j: int| 0 <= i < j < old_index + 1 ==> (arr[i] + 1 == arr[j]));
            if old_index < n - 1 {
                assert(arr[old_index] + 1 == arr[old_index + 1]);
            }
            assert(forall|i: int, j: int| 0 <= i < j < index + 1 ==> (arr[i] + 1 == arr[j]));
        }
    }
    true
}

}


//             assert(forall|i: int, j: int| 0 <= i < j < index + 1 ==> (arr[i] + 1 == arr[j]));
//   assertion failed: forall|i: int, j: int| 0 <= i < j < index + 1 ==> (arr[i] + 1 == arr[j])

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: False