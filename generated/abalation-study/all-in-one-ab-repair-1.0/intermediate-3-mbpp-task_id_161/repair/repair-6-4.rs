
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::proof()] // Will treat contains as a pure function
    fn contains(str: &Seq<i32>, key: i32) -> bool
        ensures
            result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
    {
        let mut i = 0;
        while i < str.len()
            invariant
                forall|j: int| 0 <= j < i ==> str[j] != key,
                i <= str.len(),
        {
            if (str[i] == key) {
                return true;
            }
            i += 1;
        }
        false
    }

    #[verifier::proof()]
    fn remove_elements(arr1: &Seq<i32>, arr2: &Seq<i32>) -> Seq<i32>
        ensures
            forall|i: int|
                0 <= i < result.len() ==> (arr1.contains(# [trigger] result[i]) && !arr2.contains(
                    # [trigger] result[i],
                )),
            forall|i: int|
                0 <= i < arr1.len() ==> (arr2.contains(# [trigger] arr1[i]) || result.contains(
                    # [trigger] arr1[i],
                )),
    {
        let mut output_str = seq![];
        let mut index: int = 0;
        while index < arr1.len()
            invariant
                forall|j: int|
                    0 <= j < index ==> (arr2.contains(# [trigger] arr1[j]) || output_str.contains(
                        # [trigger] arr1[j],
                    )),
                forall|j: int|
                    0 <= j < output_str.len() ==> (arr1.contains(# [trigger] output_str[j])
                        && !arr2.contains(# [trigger] output_str[j])),
                index <= arr1.len(),
                output_str.len() <= index,
        {
            if !contains(arr2, arr1[index]) {
                output_str = output_str.push(arr1[index]);
            }
            index += 1;
        }
        output_str
    }
    
    fn test_remove_elements() {
        let arr1 = vec![1, 2, 3, 4, 5];
        let arr2 = vec![2, 4];
        let seq1 = Seq::from_vec(arr1);
        let seq2 = Seq::from_vec(arr2);
        let result = remove_elements(&seq1, &seq2);
        
        assert!(result.len() == 3); // The length of the result should be 3
        assert!(result[0] == 1);
        assert!(result[1] == 3);
        assert!(result[2] == 5);
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpq22mfsgf`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: False