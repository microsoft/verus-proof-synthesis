
use vstd::prelude::*;

fn main() {}

verus! {

spec fn contains_pred(arr: Seq<i32>, key: i32) -> bool {
    exists|i: int| 0 <= i < arr.len() && arr[i] == key
}

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == contains_pred(arr@, key),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> arr[j] != key,
    {
        if arr[i] == key {
            return true;
        }
        i += 1;
    }
    false
}

fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)
    ensures
        forall|i: int| 0 <= i < shared.len() ==> contains_pred(list1@, shared[i]) && contains_pred(list2@, shared[i]),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
{
    let mut shared = Vec::new();
    let mut index = 0;
    while index < list1.len()
        invariant
            0 <= index <= list1.len(),
            forall|k: int| 0 <= k < shared.len() ==> contains_pred(list1@, shared[k]) && contains_pred(list2@, shared[k]),
            forall|k: int, l: int| 0 <= k < l < shared.len() ==> shared[k] != shared[l],
    {
        if contains(list2, list1[index]) && !contains(&shared, list1[index]) {
            shared.push(list1[index]);
        }
        index += 1;
    }
    shared
}

} // verus!

// Score: (4, 0)
// Safe: False