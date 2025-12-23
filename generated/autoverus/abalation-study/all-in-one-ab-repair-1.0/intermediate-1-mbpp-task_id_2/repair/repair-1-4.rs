
use vstd::prelude::*;

fn main() {}

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() as int && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant 0 <= i <= arr.len()
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < shared.len() as int ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() as int ==> shared[i] != shared[j],
{
    let mut shared = Vec::new();
    let mut index = 0;
    while index < list1.len()
        invariant
            0 <= index <= list1.len(),
            forall|i: int| 0 <= i < shared.len() as int ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
            forall|i: int, j: int| 0 <= i < j < shared.len() as int ==> shared[i] != shared[j]
    {
        if contains(list2, list1[index]) && !contains(&shared, list1[index]) {
            shared.push(list1[index]);
        }
        index += 1
    }
    shared
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpa7tky9q_`)
// 

// Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 1
// Safe: False