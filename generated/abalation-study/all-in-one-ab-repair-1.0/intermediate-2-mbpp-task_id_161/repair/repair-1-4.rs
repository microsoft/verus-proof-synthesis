
use vstd::prelude::*;
fn main() {}

verus! {

spec fn contains_spec(str: Seq<i32>, key: i32) -> bool {
    exists|i: int| 0 <= i < str.len() && str.index(i) == key
}

proof fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> contains_spec(str@, key),
{
    let mut i = 0;
    let mut found = false;
    while i < str.len()
        invariant
            forall|j: int| 0 <= j < i ==> str[j] != key,
            i <= str.len(),
            found == contains_spec(str@.take(i), key)
    {
        if (str[i] == key) {
            found = true;
            break;
        }
        i += 1;
    }
    found // return the result
}

fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> arr1[@i] == result[@i],
        forall|i: int|
            0 <= i < arr1.len() ==> arr2[@i] == arr1[@i] || result[@i] == arr1[@i],
{
    let mut output_str = vec![];
    
    let mut index = 0;
    while index < arr1.len()
        invariant
            forall|j: int|
                0 <= j < index ==> (arr2@.contains(#[trigger] arr1[j]) || output_str@.contains(#[trigger] arr1[j])),
            forall|j: int|
                0 <= j < output_str.len() ==> (arr1@.contains(#[trigger] output_str[j]) && !arr2@.contains(#[trigger] output_str[j])),
            index <= arr1.len()
    {
        if (!contains(&arr2, arr1[index])) {
            output_str.push(arr1[index]);
        }
        index += 1;
    }
    output_str
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp45juzp1b`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False