
use vstd::prelude::*;

fn main() {}

verus! {
    #[verifier::loop_invariant]
    fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
        ensures
            result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    {
        let mut i = 0;
        while i < arr.len()
            invariant
                0 <= i <= arr.len(),
                forall|j: int| 0 <= j < i ==> arr[j] != key,
        {
            if arr[i] == key {
                proof {
                    assert(exists|k: int| k == i && 0 <= k < arr.len() && arr[k] == key);
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
                forall|k: int| 0 <= k < index ==> (list1@.contains(#[trigger] shared[k]) && list2@.contains(#[trigger] shared[k])),
                forall|i: int, j: int| 0 <= i < j < (shared.len() as int) ==> shared[i] != shared[j],
        {
            if contains(list2, list1[index]) && !contains(&shared, list1[index]) {
                shared.push(list1[index]);
            }
            index += 1;
        }
        shared
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpdxk6zf3o`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False