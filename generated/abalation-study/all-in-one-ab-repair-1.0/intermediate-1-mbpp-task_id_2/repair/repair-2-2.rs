
use vstd::prelude::*;

fn main() {}

#[verifier::trusted]
fn contains(arr: &Vec<i32>, key: i32) -> bool {
    let mut i = 0;
    while i < arr.len() {
        if arr[i] == key {
            return true;
        }
        i += 1;
    }
    false
}

verus! {
    fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)
        ensures
            forall|i: int| 0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(#[trigger] shared[i])),
            forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
    {
        let mut shared = Vec::new();
        let mut index = 0;
        while index < list1.len()
            invariant
                0 <= index <= list1.len(),
                forall|i: int| 0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(#[trigger] shared[i])),
                forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
        {
            if contains(list2, list1[index]) && !contains(&shared, list1[index]) {
                shared.push(list1[index]);
            }
            index += 1;
        }
        shared
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpu7qx_3hj`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False