
use vstd::prelude::*;
fn main() {}
verus! {

proof fn lemma_vec_remove<T>(vec: Seq<T>, i: int)
    requires
        0 <= i < vec.len(),
    ensures
        forall |k: int| 0 <= k < i ==> #[trigger] vec[k] == vec.remove(i)[k],
        forall |k: int| i < k  < vec.len() ==> #[trigger] vec[k] ==  vec.remove(i)[k-1],
{
    
}



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
            !(exists|j: int| 0 <= j < i && (str[j] == key)),
            forall|j: int| 0 <= j < i ==> str[j] != key,
            i <= str.len(),
            str.len() == str@.len(), // specifies the length of the array
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
                0 <= i < index ==>
                arr2@.contains(arr1[i]) || output_str@.contains(arr1[i]),
            forall|i: int|
                0 <= i < output_str.len() ==> (arr1@.contains(output_str[i]) && !arr2@.contains(
                    output_str[i],
                )),
            index <= arr1.len(),
            arr1.len() == arr1@.len(), // specifies the length of arr1
            output_str.len() == output_str@.len(), // specifies the length of output_str
    {
        if (!contains(arr2, arr1[index])) {
            proof {
                lemma_vec_push(output_str@, arr1[( index ) as int], output_str.len());
            }
            output_str.push(arr1[index]);
        }
        index += 1;
        proof {
            assert(forall|i: int| 0 <= i < index ==> arr2@.contains(arr1[i]) || output_str@.contains(arr1[i]));
        }
    }
    output_str
}

} // verus!



//             assert(forall|i: int| 0 <= i < index ==> arr2@.contains(arr1[i]) || output_str@.contains(arr1[i]));
//   assertion failed: forall|i: int| 0 <= i < index ==> arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])

// Compilation Error: False, Verified: 5, Errors: 0, Verus Errors: 0
// Safe: True