
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    while index < arr.len() {
        if (arr[index] == key) {
            return true;
        }
        index += 1;
    }
    false
}

fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
{
    let mut result = Vec::new();
    let mut index = 0;
    while (index < arr1.len()) 
    // Add ghost variable to track elements added to result
    {
        if !contains(arr2, arr1[index]) && !contains(&result, arr1[index]) {
            result.push(arr1[index]);
        }
        index += 1;
        proof {
            #[verifier::invariant]
            // Invariant after each iteration
            let current_len = result.len();
            let mut is_invariant = true;
            for i in 0..index {
                if !contains(&result, arr1[( i ) as int]) && !contains(arr2, arr1[( i ) as int]) {
                    is_invariant = false;
                }
            }
            assert(is_invariant);
        }
    }
    let mut index = 0;
    while (index < arr2.len())
    {
        if !contains(arr1, arr2[index]) && !contains(&result, arr2[index]) {
            result.push(arr2[index]);
        }
        index += 1;
        proof {
            #[verifier::invariant]
            // Invariant after each iteration
            let current_len = result.len();
            let mut is_invariant = true;
            for i in 0..index {
                if !contains(&result, arr2[( i ) as int]) && !contains(arr1, arr2[( i ) as int]) {
                    is_invariant = false;
                }
            }
            assert(is_invariant);
        }
    }
    result
}

} // verus!






//             forall|i: int| 0 <= i < index ==> 
//                  (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(arr2[i])),
//   None: forall|i: int| 0 <= i < index ==>                   (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(arr2[i]))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False