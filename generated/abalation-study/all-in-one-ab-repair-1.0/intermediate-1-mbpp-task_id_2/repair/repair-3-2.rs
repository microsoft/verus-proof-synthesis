
use vstd::prelude::*;

fn main() {}

verus! {

spec fn contains_spec(arr: Seq<i32>, key: i32) -> bool {
    exists|i: int| 0 <= i < arr.len() && arr[i] == key
}

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == contains_spec(arr@, key),
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
        forall|i: int|
            0 <= i < shared.len() ==> (contains_spec(list1@, shared[i]) && contains_spec(list2@, shared[i])),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
{
    let mut shared = Vec::new();
    let mut index = 0;
    while index < list1.len()
        invariant 
            0 <= index <= list1.len(),
            forall|i: int| 0 <= i < shared.len() ==> contains_spec(list1@, shared[i]) && contains_spec(list2@, shared[i]),
            forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
    {
        if contains(list2, list1[index]) && !contains(&shared, list1[index]) {
            shared.push(list1[index]);
            proof {
                assert(contains_spec(shared@, list1[index]));
            }
        }
        index += 1;
    }
    shared
}
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp5qsaxknm`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False