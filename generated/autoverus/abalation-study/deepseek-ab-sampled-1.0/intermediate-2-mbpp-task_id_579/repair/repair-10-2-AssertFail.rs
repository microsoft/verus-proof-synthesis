
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            0 <= arr.len(),
    {
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
            0 <= i < arr1.len() ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> # [trigger] result[i] != # [trigger] result[j],
{
    let mut result = Vec::new();
    let mut index = 0;
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            0 <= arr1.len(),
            result.len() <= index,
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
            // Strengthened loop invariant to track elements from arr1
            forall|i: int| 0 <= i < index ==>
                contains(&result, arr1[i]) == (# [trigger] contains(arr2, arr1[i]) == true),
            // Ensures that all elements processed so far in arr1 that are not in arr2 are in the result
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
    {
        // For each element in arr1, process correctly
        proof {
            // Dummy proofs to assist the verifier
            assert(index == index);
        }
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            result.push(arr1[index]);
        }
        index += 1;
        // After each step, the invariant is maintained
        proof {
            assert(index <= arr1.len());
            assert(result.len() <= index);
            // Assert that all elements up to index have been processed
            // Split into two parts to help the verifier
            {
                let ghost partial_prop = 
                    forall|i: int| 0 <= i < index ==>
                        (contains(&result, arr1[i]) == contains(arr2, arr1[i]) || !contains(arr2, arr1[i]) && contains(&result, arr1[i]));
                assert(partial_prop);
            }
            {
                let ghost unique_prop = 
                    forall|i: int, j: int| 0 <= i < j < result.len() --> result[i] != result[j];
                assert(unique_prop);
            }
        }
    }
    // After processing arr1, it holds that for all processed elements in arr1, they are in result iff not in arr2
    proof {
        assert(forall|i: int| 0 <= i < arr1.len() 
            ==> (contains(&result, arr1[i]) == !contains(arr2, arr1[i])));
    }
    let mut index = 0;
    while index < arr2.len()
        invariant
            0 <= index <= arr2.len(),
            0 <= arr2.len(),
            result.len() <= index + arr1.len(),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
            // Strengthened loop invariant for arr2 processing
            forall|i: int| 0 <= i < index ==>
                contains(&result, arr2[i]) == (# [trigger] contains(arr1, arr2[i]) == true || arr2[i] in result from arr1 processing),
            // Ensures that all elements processed so far in arr2 that are not in arr1 are in the result
    {
        // For each element in arr2, process correctly
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            result.push(arr2[index]);
        }
        index += 1;
        // After each step, the invariant is maintained
        proof {
            assert(index <= arr2.len());
            assert(result.len() <= index + arr1.len());
            {
                let ghost partial_prop = 
                    forall|i: int| 0 <= i < index ==>
                        (contains(&result, arr2[i]) == contains(arr1, arr2[i]) || !contains(arr1, arr2[i]) && contains(&result, arr2[i]));
                assert(partial_prop);
            }
            {
                let ghost unique_prop = 
                    forall|i: int, j: int| 0 <= i < j < result.len() --> result[i] != result[j];
                assert(unique_prop);
            }
        }
    }
    // After processing arr2, it holds that for all processed elements in arr2, they are in result iff not in arr1
    proof {
        assert(forall|i: int| 0 <= i < arr2.len() 
            ==> (contains(&result, arr2[i]) == !contains(arr1, arr2[i])));
    }
    
    // Final proof that the required properties hold
    proof {
        let ghost prop1 = forall|i: int| 0 <= i < arr1.len() ==> 
            (!arr2@.contains(arr1[i]) ==> result@.contains(arr1[i]));
        let ghost prop2 = forall|i: int| 0 <= i < arr2.len() ==> 
            (!arr1@.contains(arr2[i]) ==> result@.contains(arr2[i]));
        let ghost prop3 = forall|i: int, j: int| 0 <= i < j < result.len() ==> 
            result[i] != result[j];
        
        assert(prop1);
        assert(prop2);
        assert(prop3);
    }
    
    result
}

}


//         assert(prop2);
//   assertion failed: prop2

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False