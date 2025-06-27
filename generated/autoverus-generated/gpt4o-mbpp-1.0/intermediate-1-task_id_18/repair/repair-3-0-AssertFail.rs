
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

fn contains(str: &Vec<char>, key: char) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            forall|j: int| 0 <= j < i ==> str[j] != key,
            forall |k:int| 0<=k<str.len() ==> str[k] == str[k], // Covered invariant for array str
            i <= str.len(),
            str.len() == str.len(), // Loop invariant for the array length
    {
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (str1@.contains(# [trigger] result[i]) && !str2@.contains(
                # [trigger] result[i],
            )),
        forall|i: int|
            0 <= i < str1.len() ==> (str2@.contains(# [trigger] str1[i]) || result@.contains(
                # [trigger] str1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;
    while index < str1.len()
        invariant
            forall|i: int|
                0 <= i < index ==> (str2@.contains(# [trigger] str1[i]) || output_str@.contains(
                    # [trigger] str1[i],
                )),
            forall|i: int|
                0 <= i < output_str.len() ==> (str1@.contains(# [trigger] output_str[i])
                    && !str2@.contains(# [trigger] output_str[i])),
            forall |k:int| 0<=k<str1.len() ==> str1[k] == str1[k], // Covered invariant for array str1
            forall |k:int| 0<=k<str2.len() ==> str2[k] == str2[k], // Covered invariant for array str2
            index <= str1.len(),
            output_str.len() <= index,
            str1.len() == str1.len(), // Loop invariant for the array length
            str2.len() == str2.len(), // Loop invariant for the array length
    {
        if (!contains(str2, str1[index])) {
            proof{
                lemma_vec_push(output_str@, str1[( index ) as int], output_str.len());
            }

            output_str.push(str1[index]);

            proof{
                assert(forall|i: int|
                    0 <= i < index + 1 ==> (str2@.contains(# [trigger] str1[i]) || output_str@.contains(
                        # [trigger] str1[i],
                    ))
                );
            }
        }
        index += 1;
    }
    output_str
}

} // verus!



//                 assert(forall|i: int|
//                     0 <= i < index + 1 ==> (str2@.contains(# [trigger] str1[i]) || output_str@.contains(
//                         # [trigger] str1[i],
//                     ))
//   assertion failed: forall|i: int|                     0 <= i < index + 1 ==> (str2@.contains(# [trigger] str1[i]) || output_str@.contains(                         # [trigger] str1[i],                     ))

// Compilation Error: False, Verified: 5, Errors: 0, Verus Errors: 0
// Safe: True