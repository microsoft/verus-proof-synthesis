
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_invariant]
struct InvariantContains {
    pub arr_len: usize,
    pub i: usize,
    pub key: i32,
}

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
            return true;
        }
        i += 1;
    }
    false
}

#[verifier::loop_invariant]
struct InvariantSharedElements {
    pub list1_len: usize,
    pub list2_len: usize,
    pub shared_len: usize,
    pub index: usize,
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
            shared.len() <= list1.len(),
            shared.len() <= list2.len(),
            forall|x: int, y: int| 
                0 <= x < y < shared.len() ==> shared[x] != shared[y],
            forall|i: int|
                0 <= i < shared.len() ==> 
                list1@.contains(#[trigger] shared[i]) && list2@.contains(#[trigger] shared[i]),
    {
        if contains(list2, list1[index]) && !contains(&shared, list1[index]) {
            shared.push(list1[index]);
        }
        index += 1;
    }
    shared
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpjvi_q0av`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False