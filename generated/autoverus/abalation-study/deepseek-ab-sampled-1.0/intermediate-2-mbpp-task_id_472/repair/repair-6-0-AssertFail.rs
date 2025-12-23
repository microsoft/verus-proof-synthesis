
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
    proof fn lemma_consecutive(arr: Seq<i32>, old_index: int)
        requires
            0 <= old_index < arr.len() as int,
            forall|i: int, j: int| 0 <= i < j <= old_index ==> (arr[i] + 1 == arr[j]),
            0 <= old_index + 1 < arr.len() as int,
            arr[old_index] + 1 == arr[old_index + 1],
        ensures
            forall|i: int, j: int| 0 <= i < j <= old_index + 1 ==> (arr[i] + 1 == arr[j]),
    {
        assert(forall|i: int, j: int| 0 <= i < j <= old_index ==> arr[i] + 1 == arr[j]);
        assert(forall|i: int, j: int| 0 <= i < j <= old_index + 1 ==>
            (i <= old_index || j <= old_index || arr[i] + 1 == arr[j]));
        assert(forall|i: int, j: int| 0 <= i < j <= old_index + 1 ==> arr[i] + 1 == arr[j]);
    }

    let mut index = 0;
    while (index < arr.len() - 1)
        invariant
            0 <= index <= arr.len() - 1,
            arr.len() > 0,
            forall|i: int, j: int| 0 <= i < j <= index ==> (arr[i] + 1 == arr[j]),
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
            assert(forall|i: int, j: int| 0 <= i < j <= old_index ==> (arr[i] + 1 == arr[j]));
            lemma_consecutive(arr@, old_index);
        }
    }
    true
}

} // verus!


//             assert(forall|i: int, j: int| 0 <= i < j <= old_index + 1 ==> (arr[i] + 1 == arr[j]));
//   assertion failed: forall|i: int, j: int| 0 <= i < j <= old_index + 1 ==> (arr[i] + 1 == arr[j])

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False