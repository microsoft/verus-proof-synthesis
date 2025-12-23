

use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= # [trigger] arr[i] + 1 < i32::MAX),
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
{
    let lemma_step = proof fn lemma(i: int, j: int) {
        assert(if j == i + 1 then (arr[i] + 1 == arr[j]) else ());
    };
    
    let mut index = 0;
    while (index < arr.len() - 1)
        invariant
            0 <= index,
            index <= arr.len(),
            arr.len() > 0,
            (forall|i: int, j: int| 0 <= i < j < index + 1 ==> (j == i + 1 ==> (arr[i] + 1 == arr[j]))),
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
            assert(forall|i: int, j: int| 0 <= i < j < old_index + 1 ==> (j == i + 1 ==> (arr[i] + 1 == arr[j])));
            assert(forall|i: int, j: int| 0 <= i < j < index + 1 ==> (j == i + 1 ==> (arr[i] + 1 == arr[j))));
        }
    }
    true
}

}

//             assert(forall|i: int, j: int| 0 <= i < j < index + 1 ==> (arr[i] + 1 == arr[j]));
//   assertion failed: forall|i: int, j: int| 0 <= i < j < index + 1 ==> (arr[i] + 1 == arr[j])

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False