
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
            // Create lemma to abstract the fact that the consecutive property holds for 1-element array
            lemma single_elem_lemma: lemma |a: i32|
                requires (0 <= a + 1 < i32::MAX),
                ensures (forall|i: int, j: int| 0 <= i < j <= 0 ==> (arr[i] + 1 == arr[j])),
            {}
            // Create lemma to abstract the fact that if the consecutive property holds for 0..index, and it holds for index, then it holds for 0..index + 1
            lemma trans Verse: lemma |old_index: int|
                requires 
                    old_index < arr.len() as int - 1,
                    0 <= old_index,
                    forall|i: int, j: int| 0 <= i < j <= old_index ==> (arr[i] + 1 == arr[j]),
                    arr[old_index] + 1 == arr[old_index + 1],
                ensures 
                    forall|i: int, j: int| 0 <= i < j <= old_index + 1 ==> (arr[i] + 1 == arr[j]),
            {}
            
            trans Verse(index - 1); // Apply lemma to prove the inductive step
        }
    }
    true
}

} // verus!


//             assert(forall|i: int, j: int| 0 <= i < j <= old_index + 1 ==> (arr[i] + 1 == arr[j]));
//   assertion failed: forall|i: int, j: int| 0 <= i < j <= old_index + 1 ==> (arr[i] + 1 == arr[j])

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False