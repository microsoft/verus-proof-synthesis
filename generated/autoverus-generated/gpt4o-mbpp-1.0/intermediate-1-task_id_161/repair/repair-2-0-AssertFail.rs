
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

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            forall|j: int| 0 <= j < i ==> str[j] != key,
            i <= str.len(),
            // Add upper and lower bound invariants for key
            key >= i32::MIN,
            key <= i32::MAX,
            // Specify the length of the array
            str.len() == str.len(),
    {
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(# [trigger] result[i]) && !arr2@.contains(
                # [trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(# [trigger] arr1[i]) || result@.contains(
                # [trigger] arr1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < arr1.len()
        invariant
            forall|j: int|
                0 <= j < index ==> (arr2@.contains(# [trigger] arr1[j]) || output_str@.contains(
                    # [trigger] arr1[j],
                )),
            forall|j: int|
                0 <= j < output_str.len() ==> (arr1@.contains(# [trigger] output_str[j])
                    && !arr2@.contains(# [trigger] output_str[j])),
            index <= arr1.len(),
            output_str.len() <= index,
            // Add upper and lower bound invariants for arr1 and arr2
            arr1.len() >= 0,
            arr1.len() <= usize::MAX,
            arr2.len() >= 0,
            arr2.len() <= usize::MAX,
            // Specify the length of the arrays
            arr1.len() == arr1.len(),
            arr2.len() == arr2.len(),
    {
        if (!contains(arr2, arr1[index])) {
            proof {
                lemma_vec_push(output_str@, arr1[( index ) as int], output_str.len());
            }
            output_str.push(arr1[index]);
        }
        index += 1;
        proof {
            assert(forall|j: int| 0 <= j < index ==> (arr2@.contains(# [trigger] arr1[j]) || output_str@.contains(# [trigger] arr1[j])));
        }
    }
    output_str
}

} // verus!



//             assert(forall|j: int| 0 <= j < index ==> (arr2@.contains(# [trigger] arr1[j]) || output_str@.contains(# [trigger] arr1[j])));
//   assertion failed: forall|j: int| 0 <= j < index ==> (arr2@.contains(# [trigger] arr1[j]) || output_str@.contains(# [trigger] arr1[j]))

// Compilation Error: False, Verified: 5, Errors: 0, Verus Errors: 0
// Safe: True