
use vstd::prelude::*;

fn main() {}

verus! {

proof fn lemma_vec_remove<T>(vec: Seq<T>, i: int)
    requires
        0 <= i < vec.len(),
    ensures
        forall |k: int| 0 <= k < i ==> #[trigger] vec[k] == vec.remove(i)[k],
        forall |k: int| i < k < vec.len() ==> #[trigger] vec[k] == vec.remove(i)[k - 1],
{
    // Base case: if i is 0, the first element is removed.
    if i == 0 {
        for k in range(0, vec.len() - 1) {
            assert(vec[k + 1] == vec.remove(i)[k]);
        }
    } else {
        // Inductive step: prove the lemma for the subsequence.
        lemma_vec_remove(vec.subrange(0, i), i - 1);
        lemma_vec_remove(vec.subrange(i + 1, vec.len()), i);
    }
}

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall |k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
    // Base case: when the vector is empty.
    if l == 0 {
        assert(vec.push(i).index(0 as int) == i);
    } else {
        // Inductive step: prove for the first element.
        assert(vec.head() == vec.push(i).head());
        lemma_vec_push(vec.tail(), i, l - 1);
    }
}

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len() {
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
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                #[trigger] arr1[i],
            )),
{
    let mut output_str = Vec::new();
    let mut index: usize = 0;

    while index < arr1.len()
        invariant
            forall |k: int| 0 <= k < output_str.len() ==> !arr2@.contains(output_str[k]),
            forall |k: int| 0 <= k < index as int ==> (arr2@.contains(arr1@[k as int]) || output_str@.contains(arr1@[k as int])),
            0 <= index <= arr1.len(),
    {
        let val = arr1[index];
        if !contains(arr2, val) {
            output_str.push(val);
            proof {
                lemma_vec_push(output_str @, val, output_str.len());
                assert(output_str@.to_set().ext_equal(output_str@.to_set().insert(val)));
            }
        }
        index += 1;
    }

    proof {
        assert(forall |i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])));

        // Use induction and the loop invariant to prove the postcondition.
        let len = arr1.len();
        let mut i = 0;
        while i < len {
            assert(arr2@.contains(arr1[i]) || output_str@.contains(arr1[i]));
            i += 1;
        }
    }

    output_str
}
}


//         assert(forall |i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])));
//   assertion failed: forall |i: int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i]))

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False