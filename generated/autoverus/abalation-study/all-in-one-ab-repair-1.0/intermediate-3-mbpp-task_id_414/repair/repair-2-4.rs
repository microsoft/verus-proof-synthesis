
use vstd::prelude::*;
fn main() {}

verus! {

spec fn contains_spec(arr: Seq<i32>, key: i32) -> bool {
    exists |i: int| 0 <= i < arr.len() && arr[i] == key
}

spec fn contains_then_not_exists(arr: Seq<i32>, key: i32, up_to: int) -> bool {
    forall |i: int| 0 <= i < up_to ==> arr[i] != key
}

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures result == contains_spec(arr@, key),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            arr.len() == old(arr.len()), // Loop invariant for array length
            contains_then_not_exists(arr@, key, i),
    {
        if arr[i] == key {
            return true;
        }
        i += 1;
    }
    false
}

spec fn any_value_exists_spec(arr1: Seq<i32>, arr2: Seq<i32>) -> bool {
    exists |k: int| 0 <= k < arr1.len() && contains_spec(arr2, arr1[k])
}

spec fn no_contains_exists(arr1: Seq<i32>, arr2: Seq<i32>, up_to: int) -> bool {
    forall |j: int| 0 <= j < up_to ==> !contains_spec(arr2, arr1[j])
}

fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    ensures result == any_value_exists_spec(arr1@, arr2@),
{
    let mut index = 0;
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            arr1.len() == old(arr1.len()), // Loop invariant for array length
            arr2.len() == old(arr2.len()), // Loop invariant for array length
            no_contains_exists(arr1@, arr2@, index),
    {
        if contains(arr2, arr1[index]) {
            return true;
        }
        index += 1;
    }
    false
}

}

fn main() {}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpfz_gpj59`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False