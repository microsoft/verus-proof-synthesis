
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
    while (index < arr.len() - 1)
        invariant
            0 <= index,
            index <= arr.len(),
            arr.len() > 0,
            forall|i: int, j: int| 0 <= i < j < index + 1 ==> (arr[i] + 1 == arr[j]),
            forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    {
        if (arr[index] + 1 != arr[index + 1]) {
            return false;
        }
        index += 1;
        proof {
            // Verify the condition for the new pair (index-1, index)
            let i = index - 1;
            let j = index;
            assert(arr[i] + 1 == arr[( j ) as int]);
            
            // Use induction to extend the forall condition
            if index - 1 >= 0 {
                assert(forall|x: int| 0 <= x < index - 1 ==> 
                    arr[x] + 1 == arr[x + 1]);
            }
            assert(forall|x: int| 0 <= x < index ==> 
                arr[x] + 1 == arr[x + 1]);
        }
    }
    true
}

}



//             assert(forall|i: int, j: int| 0 <= i < j < index + 1 ==> (arr[i] + 1 == arr[j]));
//   assertion failed: forall|i: int, j: int| 0 <= i < j < index + 1 ==> (arr[i] + 1 == arr[j])

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True