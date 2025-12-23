
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
            forall|k: int| 0 <= k < index ==> arr[k] != key, 
            index <= arr.len(),
            key == key, 
            arr.len() == arr.len() 
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
    while index < arr1.len()
        invariant
            forall|i: int|
                0 <= i < index ==> !arr2@.contains(arr1[i]) && !result@.contains(arr1[i]),
            index <= arr1.len(),
            result.len() <= index,
            forall|k: int| 0 <= k < arr1.len() ==> arr1[k] == arr1[k], 
            arr1.len() == arr1.len() 
    {
        if (!contains(arr2, arr1[index]) && !contains(&result, arr1[index])) {
            proof {
                lemma_vec_push(result@, arr1[( index ) as int], result.len());
            }
            result.push(arr1[index]);
        }
        index += 1;
    }
    index = 0;
    while index < arr2.len()
        invariant
            forall|i: int|
                0 <= i < index ==> !arr1@.contains(arr2[i]) && !result@.contains(arr2[i]),
            index <= arr2.len(),
            result.len() <= arr2.len() + arr1.len(),
            result.len() <= arr1.len() + index, 
            forall|k: int| 0 <= k < arr2.len() ==> arr2[k] == arr2[k], 
            arr2.len() == arr2.len() 
    {
        if (!contains(arr1, arr2[index]) && !contains(&result, arr2[index])) {
            proof {
                lemma_vec_push(result@, arr2[( index ) as int], result.len());
            }
            result.push(arr2[index]);
        }
        index += 1;
        proof {
            assert(forall|i: int| 0 <= i < index ==> !arr1@.contains(arr2[i]) && !result@.contains(arr2[i]));
        }
    }
    result
}

} // verus!


//             assert(forall|i: int| 0 <= i < index ==> !arr1@.contains(arr2[i]) && !result@.contains(arr2[i]));
//   assertion failed: forall|i: int| 0 <= i < index ==> !arr1@.contains(arr2[i]) && !result@.contains(arr2[i])

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True