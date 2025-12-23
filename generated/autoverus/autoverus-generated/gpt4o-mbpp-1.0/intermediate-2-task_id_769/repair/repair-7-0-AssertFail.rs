use vstd::prelude::*;
fn main() {}
verus! {
/*
 This lemma is often useful before a vector-remove call, and it can be useful to prove what element is contained in a vector.
 The parameters to this lemma function should match the executable code after it.
 Do NOT pass `old(..)' to this lemma as parameter.
 Example usage:
    proof{
	lemma_vec_remove(vec@, index);
    }
    vec.remove(index); 
 */
proof fn lemma_vec_remove<T>(vec: Seq<T>, i: int)
    requires
        0 <= i < vec.len(),
    ensures
        forall |k: int| 0 <= k < i ==> #[trigger] vec[k] == vec.remove(i)[k],
        forall |k: int| i < k  < vec.len() ==> #[trigger] vec[k] == vec.remove(i)[k-1],
{
    
}


/*
 This lemma is often useful before a vector-push call, and it can be useful to prove what element is contained in a vector.
 Example usage:
    proof{
	lemma_vec_push(vec@, value, vec.len());
    }
    vec.push(value); 
 */
proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall |k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
}

/// helper function proving the containments necessary for the assertion
proof fn lemma_difference_contains(arr1: Seq<i32>, arr2: Seq<i32>, result: Seq<i32>)
    requires
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2.contains(# [trigger] arr1[i]) ==> result.contains(arr1[i])),
    ensures
        forall |k: int| 0 <= k < arr2.len() ==> 
            (!arr1.contains(# [trigger] arr2[k]) ==> result.contains(arr2[k])),
{
    assert(forall |k: int| 0 <= k < arr2.len() ==> 
        (!arr1.contains(# [trigger] arr2[k]) ==> result.contains(arr2[k]))) by {
        // This implicitly relies on the fact that the result of the first loop contains all necessary elements
    };
}

#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    
    // Assert to ensure the invariant hold before loop
    assert(forall |k: int| 0 <= k < arr.len() ==> 
                (arr[k] == key) == (exists|j: int| 0 <= j < index && arr[j] == key));
                
    while index < arr.len()
        invariant
            // Explanation: The array 'arr' is never changed in this loop.
            forall |k: int| 0 <= k < arr.len() ==> 
                (arr[k] == key) == (exists|j: int| 0 <= j < index && arr[j] == key),
            index <= arr.len(),
            arr.len() == arr.len(),
    {
        if (arr[index] == key) {
            return true;
        }
        index += 1;
    }
    false
}

fn difference(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
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
    
    // Assert before the first loop
    assert(forall |k: int| 0 <= k < arr1.len() ==> 
                (!arr2@.contains(# [trigger] arr1[k]) ==> result@.contains(arr1[k])));
                
    while index < arr1.len()
        invariant
            // Explanation: The arrays 'arr1' and 'arr2' are never changed in this loop.
            forall |k: int| 0 <= k < arr1.len() ==> (!arr2@.contains(# [trigger] arr1[k]) ==> result@.contains(arr1[k])),
            forall|j: int, k: int|
                0 <= j < k < result.len() ==> # [trigger] result[j] != # [trigger] result[k],
            index <= arr1.len(),
            arr1.len() == arr1.len(),
            result.len() == result.len(),
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            proof {
                lemma_vec_push(result@, arr1[(index) as int], result.len());
            }
            result.push(arr1[index]);
        }
        index += 1;
    }
    index = 0;
    
    // Assert before the second loop
    proof {
        lemma_difference_contains(arr1@, arr2@, result@);
    }
    assert(forall |k: int| 0 <= k < arr2.len() ==> 
                (!arr1@.contains(# [trigger] arr2[k]) ==> result@.contains(arr2[k])));
                
    while index < arr2.len()
        invariant
            // Explanation: The arrays 'arr1' and 'arr2' are never changed in this loop.
            forall |k: int| 0 <= k < arr1.len() ==> (!arr2@.contains(# [trigger] arr1[k]) ==> result@.contains(arr1[k])),
            forall |k: int| 0 <= k < arr2.len() ==> (!arr1@.contains(# [trigger] arr2[k]) ==> result@.contains(arr2[k])),
            forall|j: int, k: int|
                0 <= j < k < result.len() ==> # [trigger] result[j] != # [trigger] result[k],
            index <= arr2.len(),
            arr2.len() == arr2.len(),
            result.len() == result.len(),
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            proof {
                lemma_vec_push(result@, arr2[(index) as int], result.len());
            }
            result.push(arr2[index]);
        }
        index += 1;
    }
    result
}

} // verus!

//     assert(forall |k: int| 0 <= k < arr2.len() ==> 
//                 (!arr1@.contains(# [trigger] arr2[k]) ==> result@.contains(arr2[k])));
//   assertion failed: forall |k: int| 0 <= k < arr2.len() ==>                  (!arr1@.contains(# [trigger] arr2[k]) ==> result@.contains(arr2[k]))

// Compilation Error: False, Verified: 4, Errors: 3, Verus Errors: 3
// Safe: True