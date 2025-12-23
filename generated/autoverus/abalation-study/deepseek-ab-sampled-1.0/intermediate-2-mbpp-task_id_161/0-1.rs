

use vstd::prelude::*;

fn main() {}

verus! {

    proof fn lemma_seq_subrange_ascend<T>(v: Seq<T>, i: int, j: int)
        requires
            0 <= i < j <= v.len(),
        ensures
            v.subrange(i as int, j as int).drop_last() == v.subrange(i as int, j-1 ),
    {
        assert(v.subrange(i as int, j as int).drop_last() =~= v.subrange(i as int, j-1));
    }

    proof fn lemma_seq_subrange_all<T>(v: Seq<T>)
        ensures
            v == v.subrange(0, v.len() as int),
    {
        assert(v =~= v.subrange(0, v.len() as int));
    }

    #[verifier::loop_isolation(false)]

    fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
        ensures
            result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
    {
        let mut i = 0;

        while (i < str.len())
            invariant
                i <= str.len(),
                0 <= i as int < str.len() as int,
                ContainsCheck: 
                    forall|j: int| 
                        0 <= j < i as int ==> !(str@.index(j) == key),
        {
            if (str[i] == key) {
                return true;
            }
            i += 1;
        }
        false
    }

    proof fn lemma_vec_remove_elements_correctness(
        arr1: Seq<i32>, 
        arr2: Seq<i32>, 
        result: Seq<i32>, 
        index: usize,
        requires 
            0 <= index <= arr1.len() as usize,
            forall|i: int| 0 <= i < index as int ==> 
                (arr2@.contains(arr1@.index(i as int)) || result@.contains(arr1@.index(i as int))),
        ensures 
            forall|i: int|
                0 <= i < index as int ==> 
                    (arr2@.contains(arr1@.index(i as int)) || result@.contains(arr1@.index(i as int))),
    ) {
        // Proof by induction on index
        if index == 0 { 
            // Base case, nothing to check
            return;
        }

        // Inductive step: assume the condition holds for index - 1, prove for index
        let prev_index = index - 1;

        lemma_vec_remove_elements_correctness(arr1, arr2, result, prev_index);

        // Check for the current element
        if !arr2@.contains(arr1@.index((prev_index as int))) {
            assert(result@.contains(arr1@.index((prev_index as int))));
        }
    }

    fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            forall|i: int|
                0 <= i < result.len() ==> 
                    (arr1@.contains(result@.index(i as int)) && !arr2@.contains(result@.index(i as int))),
            forall|i: int|
                0 <= i < arr1.len() ==> 
                    (arr2@.contains(arr1@.index(i as int)) || result@.contains(arr1@.index(i as int))),
    {
        let mut output_str = Vec::new();
        let mut index: usize = 0;

        while (index < arr1.len())
            invariant
                index <= arr1.len(),
                output_str.len() == arr1.len() - index as usize,
                AllProcessed: 
                    forall|i: int| 
                        0 <= i < index as int ==> 
                            (arr2@.contains(arr1@.index(i as int)) || output_str@.contains(arr1@.index(i as int))),
        {
            if (!contains(arr2, arr1[index])) {
                output_str.push(arr1[index]);
            }
            index += 1;
        }

        // After processing all elements, ensure the postcondition
        proof {
            lemma_vec_remove_elements_correctness(arr1@, arr2@, output_str@, arr1.len() as usize);
        }

        output_str
    }

} // verus!
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1