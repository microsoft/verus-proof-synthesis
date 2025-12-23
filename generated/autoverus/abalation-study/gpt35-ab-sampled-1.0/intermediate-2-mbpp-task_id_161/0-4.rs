
use vstd::prelude::*;

fn main() {}

verus! {

    proof fn contains_invariant(str: &Vec<i32>, key: i32, i: usize)
        ensures
            0 <= i <= str.len(),
    {
        assert(0 <= i <= str.len());
    }
    
    proof fn remove_elements_invariant(arr1: &Vec<i32>, arr2: &Vec<i32>, output_str: &Vec<i32>, index: usize)
        ensures
            0 <= index <= arr1.len(),
            output_str@ == arr1@.filter(|x: i32| !arr2@.contains(*x)),
            forall|i: int|
                0 <= i < output_str.len() ==> (arr1@.contains(output_str[i]) && !arr2@.contains(output_str[i])),
            forall|i: int|
                0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])),
    {
        assert(0 <= index <= arr1.len());
        assert(output_str@ == arr1@.filter(|x: i32| !arr2@.contains(*x)));
        assert(forall |i:int| 0 <= i < output_str.len() ==> (arr1@.contains(output_str[i]) && !arr2@.contains(output_str[i])));
        assert(forall |i:int| 0 <= i < arr1.len() ==> (arr2@.contains(arr1[i]) || output_str@.contains(arr1[i])));
    }
    
    fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
        ensures
            result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
    {
        let mut i = 0;
        while i < str.len()
            invariant
                contains_invariant(str, key, i),
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
        
        assert(output_str@ == Vec::empty());
        assert(index == 0);
        
        while index < arr1.len()
            invariant
                remove_elements_invariant(arr1, arr2, output_str, index),
        {
            if (!contains(arr2, arr1[index])) {
                output_str.push(arr1[index]);
            }
            index += 1;
        }
        output_str
    }

} // verus!

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4