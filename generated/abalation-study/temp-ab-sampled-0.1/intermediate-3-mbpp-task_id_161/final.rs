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
    proof {
        assert(exists|j: int|
            0 <= j < str.len() ==> (str[j] == key) <==> (exists|k: int|
                0 <= k < str.len() && (str[k] == key))); // Modified by AI, for assertion fail
    }
    while i < str.len()
        invariant
            exists|j: int|
                0 <= j < i ==> (str[j] == key) <==> (exists|k: int|
                    0 <= k < str.len() && (str[k] == key)),
            i <= str.len(),
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
            forall|i: int|
                0 <= i < index ==> (arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(
                    # [trigger] arr1[i],
                )),
            forall|i: int|
                0 <= i < output_str.len() ==> (arr1@.contains(# [trigger] output_str[i])
                    && !arr2@.contains(# [trigger] output_str[i])),
            forall|k: int| 0 <= k < arr1.len() ==> arr1[k] == arr1[k], // arr1 is never changed in the loop
            forall|k: int| 0 <= k < arr2.len() ==> arr2[k] == arr2[k], // arr2 is never changed in the loop
            index <= arr1.len(),
            output_str.len() <= index, // Modified by AI, for assertion fail
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
            assert(forall|i: int|
                0 <= i < index ==> (arr2@.contains(# [trigger] arr1[i]) || output_str@.contains(
                    # [trigger] arr1[i],
                )));
        } // Added by AI
    }
    output_str
}

} // verus!
// Score: Compilation Error: False, Verified: 4, Errors: 1, Verus Errors: 3