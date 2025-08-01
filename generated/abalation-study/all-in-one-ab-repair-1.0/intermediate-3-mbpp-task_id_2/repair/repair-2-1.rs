
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len() {
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> (arr[j] != key); // Ensuring elements up to i are not key
        if arr[i] == key {
            return true;
        }
        i += 1;
    }
    false
}

fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)
    ensures
        forall|i: int| 0 <= i < shared.len() ==> list1@.contains(#[trigger] shared[i]) && list2@.contains(#[trigger] shared[i]),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
{
    let mut shared = Vec::new();
    let mut index = 0;
    while index < list1.len() {
        invariant
            0 <= index <= list1.len(),
            forall|i: int| 0 <= i < shared.len() ==> list1@.contains(#[trigger] shared[i]) && list2@.contains(#[trigger] shared[i]),
            forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
            forall|i: int| 0 <= i < index ==> contains(&list1, list1[i]) ==> contains(&list2, list1[i]) ==> (contains(&shared, list1[i]) || !list1@.contains(list1[i])); // Added by AI
        if contains(list2, list1[index]) && !contains(&shared, list1[index]) {
            shared.push(list1[index]);
        }
        index += 1;
    }
    shared
}
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp4vcky02x`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False