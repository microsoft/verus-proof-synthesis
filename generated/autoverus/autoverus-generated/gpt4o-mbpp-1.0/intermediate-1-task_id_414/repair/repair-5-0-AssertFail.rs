
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
    let mut i = 0;

    assert(forall |k:int| 0 <= k < arr.len() ==> (arr[k] != key || (exists|m: int| 0 <= m < i && arr[m] == key))); // Assert to ensure the invariant holds before entering the loop

    while i < arr.len()
        invariant
            arr.len() == arr.len(), // Invariant specifying the length of the array
            forall |k:int| 0 <= k < arr.len() ==> (arr[k] != key || (exists|m: int|
                    0 <= m < i && arr[m] == key)), // Updated to cover every element of arr since arr is never changed in the loop
            i <= arr.len(),
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;

        // Proving the invariant after incrementing i
        assert(forall |k:int| 0 <= k < arr.len() ==> (arr[k] != key || (exists|m: int| 0 <= m < i && arr[m] == key)));
    }
    false
}

fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    ensures
        result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(# [trigger] arr1[k]),
{
    let mut index = 0;

    assert(arr2.len() <= 0 || forall |k:int| 0 <= k < arr1.len() ==> (arr2@.contains(# [trigger] arr1[k]) ==> (exists|m: int| 0 <= m < index && arr2@.contains(# [trigger] arr1[m])))); // Assert to ensure invariant holds before entering the loop

    while index < arr1.len()
        invariant
            arr1.len() == arr1.len(), // Invariant specifying the length of arr1
            arr2.len() == arr2.len(), // Invariant specifying the length of arr2
            arr2.len() <= 0 || forall |k:int| 0 <= k < arr1.len() ==> (arr2@.contains(# [trigger] arr1[k]) ==> (exists|m: int| 0 <= m < index && arr2@.contains(# [trigger] arr1[m]))), // Updated to cover every element of arr1 and arr2 since they are never changed in the loop
            index <= arr1.len(),
    {
        if (contains(arr2, arr1[index])) {
            return true;
        }
        index += 1;

        proof{
            lemma_vec_push(arr2@, arr1[index as usize], arr2.len());
        }

        // Proving the invariant after incrementing index
        assert(arr2.len() <= 0 || forall |k:int| 0 <= k < arr1.len() ==> (arr2@.contains(# [trigger] arr1[k]) ==> (exists|m: int| 0 <= m < index && arr2@.contains(# [trigger] arr1[m]))));
    }
    false
}

} // verus!


//     assert(arr2.len() <= 0 || forall |k:int| 0 <= k < arr1.len() ==> (arr2@.contains(# [trigger] arr1[k]) ==> (exists|m: int| 0 <= m < index && arr2@.contains(# [trigger] arr1[m])))); // Assert to ensure invariant holds before entering the loop
//   assertion failed: arr2.len() <= 0 || forall |k:int| 0 <= k < arr1.len() ==> (arr2@.contains(# [trigger] arr1[k]) ==> (exists|m: int| 0 <= m < index && arr2@.contains(# [trigger] arr1[m])))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: True