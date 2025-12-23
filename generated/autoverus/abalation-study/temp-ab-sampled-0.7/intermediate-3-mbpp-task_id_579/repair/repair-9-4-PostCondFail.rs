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
        forall |k: int| i < k  < vec.len() ==> #[trigger] vec[k] ==  vec.remove(i)[k-1],
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



#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|i: int| 0 <= i < index ==> arr[i] != key,
            forall|k: int| 0 <= k < arr.len() ==> arr[k] == arr[k], // Added invariant to cover all elements in arr
            0 <= index <= arr.len(), // Repeating invariant
            arr.len() == arr.len(), // Array length invariant
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
            forall|i: int, j: int|
                0 <= i < j < result.len() ==> # [trigger] result[i] != # [trigger] result[j],
            forall|i: int|
                0 <= i < index ==> !arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(
                    arr1[i],
                ),
            forall|k: int| 0 <= k < arr1.len() ==> arr1[k] == arr1[k], // Added invariant to cover all elements in arr1
            forall|k: int| 0 <= k < arr2.len() ==> arr2[k] == arr2[k], // Added invariant to cover all elements in arr2
            0 <= index <= arr1.len(), // Repeating invariant
            arr1.len() == arr1.len(), // Array length invariant for arr1
            arr2.len() == arr2.len(), // Array length invariant for arr2
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            proof {
                lemma_vec_push(result@, arr1[( index ) as int], result.len());
            }
            result.push(arr1[index]);
        }
        index += 1;
    }
    let mut index = 0;
    while index < arr2.len()
        invariant
            0 <= index <= arr2.len(),
            forall|i: int, j: int|
                0 <= i < j < result.len() ==> # [trigger] result[i] != # [trigger] result[j],
            forall|i: int|
                0 <= i < index ==> !arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(
                    arr2[i],
                ),
            forall|k: int| 0 <= k < arr1.len() ==> arr1[k] == arr1[k], // Added invariant to cover all elements in arr1
            forall|k: int| 0 <= k < arr2.len() ==> arr2[k] == arr2[k], // Added invariant to cover all elements in arr2
            0 <= index <= arr2.len(), // Repeating invariant
            arr1.len() == arr1.len(), // Array length invariant for arr1
            arr2.len() == arr2.len(), // Array length invariant for arr2
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            proof {
                lemma_vec_push(result@, arr2[( index ) as int], result.len());
            }
            result.push(arr2[index]);
        }
        index += 1;
    }
    proof {
        forall|i: int| 0 <= i < arr1.len() ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(arr1[i]));
        forall|i: int| 0 <= i < arr2.len() ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(arr2[i]));
    } // Added by AI
    result
}

} // verus!

// failed this postcondition
//         forall|i: int|
//             0 <= i < arr1.len() ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(
//                 arr1[i],
//             )),
// at the end of the function body
// {
//     let mut result = Vec::new();
//     let mut index = 0;
//     while index < arr1.len()
// ...
//     result
// }
//   at the end of the function body: {     let mut result = Vec::new();     let mut index = 0;     while index < arr1.len()         invariant             0 <= index <= arr1.len(),             forall|i: int, j: int|                 0 <= i < j < result.len() ==> # [trigger] result[i] != # [trigger] result[j],             forall|i: int|                 0 <= i < index ==> !arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(                     arr1[i],                 ),             forall|k: int| 0 <= k < arr1.len() ==> arr1[k] == arr1[k], // Added invariant to cover all elements in arr1             forall|k: int| 0 <= k < arr2.len() ==> arr2[k] == arr2[k], // Added invariant to cover all elements in arr2             0 <= index <= arr1.len(), // Repeating invariant             arr1.len() == arr1.len(), // Array length invariant for arr1             arr2.len() == arr2.len(), // Array length invariant for arr2     {         if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {             proof {                 lemma_vec_push(result@, arr1[( index ) as int], result.len());             }             result.push(arr1[index]);         }         index += 1;     }     let mut index = 0;     while index < arr2.len()         invariant             0 <= index <= arr2.len(),             forall|i: int, j: int|                 0 <= i < j < result.len() ==> # [trigger] result[i] != # [trigger] result[j],             forall|i: int|                 0 <= i < index ==> !arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(                     arr2[i],                 ),             forall|k: int| 0 <= k < arr1.len() ==> arr1[k] == arr1[k], // Added invariant to cover all elements in arr1             forall|k: int| 0 <= k < arr2.len() ==> arr2[k] == arr2[k], // Added invariant to cover all elements in arr2             0 <= index <= arr2.len(), // Repeating invariant             arr1.len() == arr1.len(), // Array length invariant for arr1             arr2.len() == arr2.len(), // Array length invariant for arr2     {         if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {             proof {                 lemma_vec_push(result@, arr2[( index ) as int], result.len());             }             result.push(arr2[index]);         }         index += 1;     }     proof {         forall|i: int| 0 <= i < arr1.len() ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(arr1[i]));         forall|i: int| 0 <= i < arr2.len() ==> (!arr1@.contains(# [trigger] arr2[i]) ==> result@.contains(arr2[i]));     } // Added by AI     result }
//   failed this postcondition: forall|i: int|             0 <= i < arr1.len() ==> (!arr2@.contains(# [trigger] arr1[i]) ==> result@.contains(                 arr1[i],             ))

// Compilation Error: False, Verified: 5, Errors: 1, Verus Errors: 1
// Safe: True