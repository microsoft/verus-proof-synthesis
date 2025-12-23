
use vstd::prelude::*;

fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
        ensures
            result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    {
        let mut i = 0;
        while i < arr.len()
            invariant
                0 <= i <= arr.len(),
                exists|j: int| 0 <= j < i && arr[j] == key ==> result == true
        {
            if arr[i] == key {
                proof {
                    assert(exists|j: int| 0 <= j < arr.len() && (arr[j] == key));
                }
                return true;
            }
            i += 1;
        }
        false
    }

    fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)
        ensures
            forall|i: int|
                0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                    #[trigger] shared[i],
                )),
            forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
    {
        let mut shared = Vec::new();
        let mut index = 0;
        while index < list1.len()
            invariant
                0 <= index <= list1.len(),
                forall|i: int| 0 <= i < shared.len() ==> list1@.contains(shared[i]) && list2@.contains(shared[i]),
                forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j]
        {
            if contains(list2, list1[index]) && !contains(&shared, list1[index]) {
                shared.push(list1[index]);
            }
            index += 1;
        }
        shared
    }
} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 3


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp5mcpbkww`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False